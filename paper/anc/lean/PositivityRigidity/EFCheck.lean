/-
Consistency check of the ledger axiom `explicit_formula` (Lemma 2.3) against a proved theorem.

Zeta23 (the Lean formalisation of Alpöge–Furman, arXiv:2608.13637) proves the Weil explicit formula for
`ζ`, with no hypotheses, for test functions `F = paperFT k`, `k ∈ C_c²(ℝ)`
(`Zeta23.WeilEF.EF_lit_zetaZeroConfig`).  For even, real `k` such `F` lie in the test class `𝒯`
(`paperFT_mem_TestClass`), and we show that the conclusion of the ledger axiom `explicit_formula` holds
for them as a *theorem* (`explicit_formula_of_paleyWiener`), without using any ledger axiom (this file
imports only `Basic.lean` and Zeta23).  So the normalisation of the axiom — `t_ρ = −i(ρ − 1/2)`, the
multiplicities, `ξ_n = log n/(2π)`, the factor `1/π`, the archimedean density
`(1/2π)(Re ψ(1/4 + it/2) − log π)`, the real part taken in `Arch` — agrees with a proved explicit formula
on the Paley–Wiener subclass `{F ∈ 𝒯 : F̂ ∈ C_c²}`.
-/
import PositivityRigidity.Basic
import Zeta23.WeilEF.Main

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-! ## Symmetries of `paperFT k` for even real `k` -/

/-- For `k` even and real, `k̃(u) = conj k(−u) = k(u)`. -/
theorem tilde_eq_self_of_even_real {k : ℝ → ℂ} (heven : ∀ u, k (-u) = k u)
    (hreal : ∀ u, (k u).im = 0) : Zeta23.EF.tilde k = k := by
  funext u
  simp only [Zeta23.EF.tilde]
  rw [heven u]
  exact Complex.conj_eq_iff_im.mpr (hreal u)

/-- For `k` even and real, `paperFT k z = conj (paperFT k (conj z))`. -/
theorem paperFT_eq_conj {k : ℝ → ℂ} (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0)
    (z : ℂ) : Zeta23.paperFT k z = (starRingEnd ℂ) (Zeta23.paperFT k ((starRingEnd ℂ) z)) := by
  have h := Zeta23.EF.paperFT_tilde k z
  rwa [tilde_eq_self_of_even_real heven hreal] at h

/-- For `k` even and real, `paperFT k` is real on `ℝ`. -/
theorem paperFT_real {k : ℝ → ℂ} (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0)
    (t : ℝ) : (Zeta23.paperFT k t).im = 0 := by
  have h := paperFT_eq_conj heven hreal (t : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- For `k` even and real, `paperFT k (i/2) + paperFT k (−i/2)` is real. -/
theorem paperFT_poles_real {k : ℝ → ℂ} (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0) :
    (Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2)).im = 0 := by
  have h := paperFT_eq_conj heven hreal (I / 2)
  have hc : (starRingEnd ℂ) (I / 2) = -I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  rw [hc] at h
  rw [h, Complex.add_im, Complex.conj_im]
  ring

/-- For `k` even, `paperFT k` is even. -/
theorem paperFT_even {k : ℝ → ℂ} (heven : ∀ u, k (-u) = k u) (z : ℂ) :
    Zeta23.paperFT k (-z) = Zeta23.paperFT k z := by
  unfold Zeta23.paperFT
  rw [← integral_neg_eq_self]
  congr 1
  funext u
  rw [heven u]
  push_cast
  ring_nf

/-! ## The transform of `paperFT k` -/

/-- Fourier inversion: `(paperFT k)^(ξ) = 2π k(2πξ)`. -/
theorem FT_paperFT {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (ξ : ℝ) :
    FT (Zeta23.paperFT k) ξ = 2 * Real.pi * k (2 * Real.pi * ξ) := by
  have hcont : Continuous k := hk.continuous
  have hint : Integrable k := hcont.integrable_of_hasCompactSupport hkc
  have hFk := Zeta23.EF.integrable_fourier_of_contDiff_two hk hkc
  have hinv := Zeta23.EF.paper_inversion hcont hint hFk (2 * Real.pi * ξ)
  unfold FT onR
  rw [Real.fourier_real_eq_integral_exp_smul, hinv, ← mul_assoc]
  have h2pi : (2 * (Real.pi : ℂ)) * (1 / (2 * (Real.pi : ℂ))) = 1 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp
  rw [h2pi, one_mul]
  congr 1
  funext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-! ## `paperFT k` lies in the test class -/

/-- For `k ∈ C_c²(ℝ)` even and real, `paperFT k ∈ 𝒯_δ` for every `δ ∈ (0, 1/2)` (Definition 2.1). -/
theorem paperFT_inTδ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0) {δ : ℝ} (h0 : 0 < δ)
    (h1 : δ < 1 / 2) : InTδ δ (Zeta23.paperFT k) := by
  obtain ⟨Λ, hΛ⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  have hint : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  refine ⟨h0, h1, fun z _ => paperFT_even heven z, paperFT_real heven hreal,
    fun z _ => (Zeta23.WeilEF.differentiable_paperFT hk.continuous hkc).analyticAt z, ?_⟩
  set b : ℝ := 1 / 2 + δ
  set A : ℝ := ∫ u, ‖k u‖
  set B : ℝ := ∫ u, ‖deriv (deriv k) u‖
  have hA : 0 ≤ A := integral_nonneg fun u => norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun u => norm_nonneg _
  refine ⟨2 * Real.exp (b * |Λ|) * (A + B), fun z hz => ?_⟩
  have hzb : |z.im| ≤ b := hz
  have hexp : Real.exp (|z.im| * Λ) ≤ Real.exp (b * |Λ|) := by
    apply Real.exp_le_exp.mpr
    calc |z.im| * Λ ≤ |z.im| * |Λ| := mul_le_mul_of_nonneg_left (le_abs_self Λ) (abs_nonneg _)
      _ ≤ b * |Λ| := mul_le_mul_of_nonneg_right hzb (abs_nonneg _)
  have e1 := Zeta23.norm_paperFT_le hint hΛ z
  have e2 := Zeta23.norm_paperFT_mul_sq_le hk hΛ z
  have hE : 0 ≤ Real.exp (b * |Λ|) := (Real.exp_pos _).le
  have hn : 0 ≤ ‖Zeta23.paperFT k z‖ := norm_nonneg _
  have hsq : (1 + ‖z‖) ^ 2 ≤ 2 * (1 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖z‖ - 1)]
  calc (1 + ‖z‖) ^ 2 * ‖Zeta23.paperFT k z‖
      ≤ 2 * (1 + ‖z‖ ^ 2) * ‖Zeta23.paperFT k z‖ := mul_le_mul_of_nonneg_right hsq hn
    _ = 2 * (‖Zeta23.paperFT k z‖ + ‖Zeta23.paperFT k z‖ * ‖z‖ ^ 2) := by ring
    _ ≤ 2 * (Real.exp (|z.im| * Λ) * A + Real.exp (|z.im| * Λ) * B) := by gcongr
    _ ≤ 2 * (Real.exp (b * |Λ|) * A + Real.exp (b * |Λ|) * B) := by gcongr
    _ = 2 * Real.exp (b * |Λ|) * (A + B) := by ring

theorem paperFT_mem_TestClass {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0) :
    Zeta23.paperFT k ∈ TestClass :=
  ⟨1 / 4, paperFT_inTδ hk hkc heven hreal (by norm_num) (by norm_num)⟩

/-! ## The check -/

/-- `γ_ρ = (ρ − 1/2)/i` (Zeta23) is `t_ρ = −i(ρ − 1/2)` (Lemma 2.3). -/
theorem gammaOf_eq_tOf (ρ : ℂ) : Zeta23.gammaOf ρ = tOf ρ := by
  unfold Zeta23.gammaOf tOf
  rw [Complex.div_I]
  ring

/-- The archimedean side: `𝒜(F) = F(i/2) + F(−i/2) + (1/2π) ∫ F(r)(Re ψ(1/4 + ir/2) − log π) dr`. -/
theorem Arch_paperFT {k : ℝ → ℂ} (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0) :
    ((Arch (Zeta23.paperFT k) : ℝ) : ℂ) =
      Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) +
        (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) := by
  unfold Arch
  push_cast
  have hpole : (((Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2)).re : ℝ) : ℂ) =
      Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) :=
    Complex.ext (by simp) (by simp [paperFT_poles_real heven hreal])
  have hint : ((∫ t : ℝ, (Zeta23.paperFT k t).re * Ωinf t : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    congr 1
    funext t
    have hre : (((Zeta23.paperFT k t).re : ℝ) : ℂ) = Zeta23.paperFT k t :=
      Complex.ext (by simp) (by simp [paperFT_real heven hreal t])
    have hΩ : Ωinf t = (1 / (2 * Real.pi)) * Zeta23.EF.gammaBracket t := rfl
    rw [hΩ]
    push_cast
    rw [hre]
    ring
  rw [hpole, hint]

/-- The prime side: `(1/π) Σ Λ(n) n^{-1/2} F̂(ξ_n) = Σ Λ(n) n^{-1/2} (k(log n) + k(−log n))`. -/
theorem prime_paperFT {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (heven : ∀ u, k (-u) = k u) :
    (1 / Real.pi : ℂ) * ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        FT (Zeta23.paperFT k) (xiOf n) =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [FT_paperFT hk hkc, heven]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hx : 2 * Real.pi * xiOf n = Real.log n := by
    unfold xiOf; field_simp
  rw [hx]
  field_simp
  ring

/-- **The explicit formula on the Paley–Wiener class, as a theorem.**  For `k ∈ C_c²(ℝ)` even and real
and `F = paperFT k` (`F(z) = ∫ k(u) e^{izu} du`, so `F ∈ 𝒯` by `paperFT_mem_TestClass`), the conclusion
of the ledger axiom `explicit_formula` holds, proved from Zeta23's hypothesis-free explicit formula
`Zeta23.WeilEF.EF_lit_zetaZeroConfig` and no ledger axiom. -/
theorem explicit_formula_of_paleyWiener (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (heven : ∀ u, k (-u) = k u) (hreal : ∀ u, (k u).im = 0)
    (F : ℂ → ℂ) (hF : F = Zeta23.paperFT k) :
    Summable (fun ρ : NontrivialZeros => (mult ρ : ℂ) * F (tOf ρ)) ∧
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n)) ∧
    ((Arch F : ℝ) : ℂ) = (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * F (tOf ρ)) +
      (1 / Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n) := by
  subst hF
  obtain ⟨hsum, hEF⟩ := Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hkc
  -- the zero sums are the same sum
  have hfun : (fun ρ : NontrivialZeros => (mult ρ : ℂ) * Zeta23.paperFT k (tOf ρ)) =
      (fun ρ : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) := by
    funext ρ
    rw [gammaOf_eq_tOf]
    rfl
  -- the prime sum has finite support
  have hprime : Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (Zeta23.paperFT k) (xiOf n)) := by
    obtain ⟨Λ, hΛ⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
    apply summable_of_hasFiniteSupport
    apply (Finset.range (⌈Real.exp Λ⌉₊ + 1)).finite_toSet.subset
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    push Not at hge
    apply hn
    have hn1 : (1 : ℝ) ≤ n := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have hlog : Λ < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have h1 : (⌈Real.exp Λ⌉₊ : ℝ) < n := by exact_mod_cast (by omega : ⌈Real.exp Λ⌉₊ < n)
      exact lt_of_le_of_lt (Nat.le_ceil _) h1
    have hk0 : k (Real.log n) = 0 := by
      by_contra hne
      have := hΛ _ hne
      rw [abs_of_nonneg (Real.log_nonneg hn1)] at this
      linarith
    have hx : 2 * Real.pi * xiOf n = Real.log n := by
      unfold xiOf; field_simp
    rw [FT_paperFT hk hkc, hx, hk0]
    ring
  have hEF' : (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * Zeta23.paperFT k (tOf ρ)) =
      Zeta23.EF.literatureRHS k := by
    simp only [gammaOf_eq_tOf] at hEF
    exact hEF
  refine ⟨hfun ▸ hsum, hprime, ?_⟩
  rw [Arch_paperFT heven hreal, prime_paperFT hk hkc heven, hEF']
  unfold Zeta23.EF.literatureRHS
  ring

end PosRig
