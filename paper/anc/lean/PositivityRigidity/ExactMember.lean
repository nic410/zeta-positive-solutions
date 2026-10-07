/-
v1.2: the exact members `F_J = Ξ² P_J(t²)` of Proposition 4.5 in the cone, without a cushion, and the certified
numbers they give.

* `Ffam_mem_Cone_of`, `Ffam_mem_ConeOPS_of`: `F_J ∈ 𝒞` (resp. `𝒞_OPS`) as soon as every coefficient of `P_J` is
  non-negative and `F̂_J ≥ 0` on `[ξ₂, ∞)` (resp. on `[0, ∞)`: `F̂_J` is even, `FT_neg_of_even`).  `F_J ∈ 𝒯` is
  Proposition 4.5 (`Ffam_mem_TestClass`, from the bound (4.1)), and `F_J ≥ Ξ²` is `Ffam_ge_Xi_sq` (`P_J(0) = 1`).
* `prop_exact_cone` (Proposition 5.7, exact members in the cone): for the five rows of
  Table 1 (`J = 10, 60, 61, 110, 111`; ledger certificate `cert_exact_cone`, and Proposition 5.6, `cert_finiteJ`,
  for the coefficients), `F_J ≥ Ξ²`, `F_J ∈ 𝒞_OPS ⊆ 𝒞`, and `𝒜(F_J)` is the prime-power tail sum, with the certified
  bounds for `𝒜(F_J)` and `∫ F_J`.
* `thm_5_1` (Theorem 5.1): `κ* ≤ κ*_OPS ≤ κ_J` for every row, in particular `κ* ≤ κ*_OPS ≤ 1.4291572 · 10^{-1060}`
  (`J = 111`).
* `cor_5_2`, `cor_5_2_RH` (Corollary 5.2): `q_min ≥ 1 − 8.98 · 10^{-1060}`, the classical conductor bound
  `e^{−2πκ*_OPS}` is at least `1 − 8.98 · 10^{-1060}` too, and under RH `1 − 8.98 · 10^{-1060} ≤ q_min ≤ 1`.
* `exact111_near_rigidity`: the facts about `F₁₁₁` used by Corollary 5.3 (`NearRigidity.lean`).

The arithmetic that combines the certified bounds (`A_J/I_J ≤ κ_J`, `2πκ₁₁₁ ≤ 8.9796596 · 10^{-1060}`, …) is done
in Lean.
-/
import PositivityRigidity.Certified
import PositivityRigidity.ZeroSupport

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

set_option exponentiation.threshold 2000

/-! ## The exact members in the cones -/

/-- The Fourier transform of a function that is even on `ℝ` is even. -/
theorem FT_neg_of_even (F : ℂ → ℂ) (heven : ∀ t : ℝ, F (-(t : ℂ)) = F t) (ξ : ℝ) :
    FT F (-ξ) = FT F ξ := by
  unfold FT onR
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_neg_eq_self]
  congr 1
  funext v
  have h1 : F ((-v : ℝ) : ℂ) = F v := by rw [Complex.ofReal_neg, heven v]
  rw [h1]
  congr 2
  push_cast
  ring

/-- `F_J` is even. -/
theorem Ffam_even (J : ℕ) (z : ℂ) : Ffam J (-z) = Ffam J z := by
  simp only [Ffam, Xi_even, Hfam_even]

/-- `F_J` on the real line, as a real number: `F_J(t) = Ξ(t)² Σ_{k ≤ 2J} p_k t^{2k}`. -/
theorem Ffam_ofReal (J : ℕ) (t : ℝ) :
    Ffam J t =
      (((Xi t).re ^ 2 * ∑ k ∈ Finset.range (2 * J + 1), pcoef J k * (t ^ 2) ^ k : ℝ) : ℂ) := by
  set x := (Xi t).re with hx
  have hX : Xi t = (x : ℂ) := Complex.ext (by simp [hx]) (by simp [Xi_real t])
  unfold Ffam
  rw [Hfam_ofReal, hX]
  push_cast
  ring

/-- `P_J(t²) ≥ P_J(0) = 1` on `ℝ` when every coefficient of `P_J` is non-negative. -/
theorem one_le_sum_pcoef {J : ℕ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k) (t : ℝ) :
    1 ≤ ∑ k ∈ Finset.range (2 * J + 1), pcoef J k * (t ^ 2) ^ k := by
  have h0 : (0 : ℕ) ∈ Finset.range (2 * J + 1) := by simp
  have := Finset.single_le_sum (f := fun k => pcoef J k * (t ^ 2) ^ k)
    (fun k hk => mul_nonneg (hpos k (by have := Finset.mem_range.mp hk; omega)) (by positivity)) h0
  simpa [pcoef] using this

/-- **`F_J ≥ Ξ²` on `ℝ`** when every coefficient of `P_J` is non-negative (`H_J ≥ P_J(0) = 1`; for the certified
`J` this is Proposition 5.6). -/
theorem Ffam_ge_Xi_sq {J : ℕ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k) (t : ℝ) :
    (Xi t ^ 2).re ≤ (Ffam J t).re := by
  rw [Ffam_ofReal, Complex.ofReal_re, Xi_sq_re]
  have h1 := one_le_sum_pcoef hpos t
  have h3 : 0 ≤ (Xi t).re ^ 2 := sq_nonneg _
  nlinarith

/-- `F_J ≥ 0` on `ℝ` (in `ℂ`'s order) when every coefficient of `P_J` is non-negative. -/
theorem Ffam_nonneg {J : ℕ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k) (t : ℝ) : 0 ≤ Ffam J t := by
  rw [Ffam_ofReal]
  exact Complex.zero_le_real.mpr
    (mul_nonneg (sq_nonneg _) (zero_le_one.trans (one_le_sum_pcoef hpos t)))

/-- `F̂_J` is real-valued (`F_J` is even and real on `ℝ`), so `0 ≤ Re F̂_J(ξ)` is `0 ≤ F̂_J(ξ)` in `ℂ`'s order. -/
theorem FT_Ffam_nonneg_of_re {J : ℕ} {ξ : ℝ} (h : 0 ≤ (FT (Ffam J) ξ).re) : 0 ≤ FT (Ffam J) ξ := by
  have him : (FT (Ffam J) ξ).im = 0 :=
    FT_real_of_even_real (Ffam J) (fun t => Ffam_even J t)
      (fun t => by rw [Ffam_ofReal]; exact Complex.ofReal_im _) ξ
  exact Complex.nonneg_iff.mpr ⟨h, him.symm⟩

/-- **`F_J ∈ 𝒞`** from non-negative coefficients of `P_J` and `F̂_J ≥ 0` on `[ξ₂, ∞)` (`F_J ∈ 𝒯` is
Proposition 4.5, from the bound (4.1)). -/
theorem Ffam_mem_Cone_of {J : ℕ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k)
    (hW : ∀ ξ : ℝ, xi2 ≤ ξ → 0 ≤ (FT (Ffam J) ξ).re) : Ffam J ∈ Cone :=
  ⟨Ffam_mem_TestClass J, Ffam_nonneg hpos, fun ξ hξ => FT_Ffam_nonneg_of_re (hW ξ hξ)⟩

/-- **`F_J ∈ 𝒞_OPS`** from non-negative coefficients of `P_J` and `F̂_J ≥ 0` on `[0, ∞)`: `F̂_J` is even. -/
theorem Ffam_mem_ConeOPS_of {J : ℕ} (hpos : ∀ k ≤ 2 * J, 0 ≤ pcoef J k)
    (hW : ∀ ξ : ℝ, 0 ≤ ξ → 0 ≤ (FT (Ffam J) ξ).re) : Ffam J ∈ ConeOPS := by
  refine ⟨Ffam_mem_TestClass J, Ffam_nonneg hpos, fun ξ => FT_Ffam_nonneg_of_re ?_⟩
  rcases le_or_gt 0 ξ with h | h
  · exact hW ξ h
  · have he := FT_neg_of_even (Ffam J) (fun t => Ffam_even J t) (-ξ)
    rw [neg_neg] at he
    rw [he]
    exact hW (-ξ) (by linarith)

/-! ## Proposition 5.7: the exact members in the cone -/

/-- Proposition 5.6: for the certified `J`, every coefficient of `P_J` is positive. -/
theorem pcoef_nonneg_of_finiteJ {J : ℕ} (hJ : J ∈ ({10, 60, 61, 110, 111} : Finset ℕ)) :
    ∀ k ≤ 2 * J, 0 ≤ pcoef J k :=
  fun k hk => ((cert_finiteJ J hJ).2 k hk).1.le

theorem exactMembers_J {row : ExactRow} (h : row ∈ exactMembers) :
    row.J ∈ ({10, 60, 61, 110, 111} : Finset ℕ) := by
  simp only [exactMembers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The certified facts about the rows of Table 1, without the formula for `𝒜(F_J)`: `F_J ≥ Ξ²`,
`F_J ∈ 𝒞_OPS ⊆ 𝒞`, `𝒜(F_J) ≤ A_J`, `∫ F_J ≥ I_J`. -/
theorem exact_cone_facts : ∀ row ∈ exactMembers,
    (∀ t : ℝ, (Xi t ^ 2).re ≤ (Ffam row.J t).re) ∧ Ffam row.J ∈ ConeOPS ∧ Ffam row.J ∈ Cone ∧
    Arch (Ffam row.J) ≤ (row.archUp : ℝ) ∧ (row.intLo : ℝ) ≤ intR (Ffam row.J) := by
  intro row hrow
  obtain ⟨hW, hA, hI⟩ := cert_exact_cone row hrow
  have hpos := pcoef_nonneg_of_finiteJ (exactMembers_J hrow)
  have hOPS := Ffam_mem_ConeOPS_of hpos hW
  exact ⟨Ffam_ge_Xi_sq hpos, hOPS, ConeOPS_subset_Cone hOPS, hA, hI⟩

/-- **Proposition 5.7 (exact members in the cone).**  For every row of Table 1
(`exactMembers`: `J = 10, 60, 61, 110, 111`), the exact member `F_J = Ξ² P_J(t²)` of Proposition 4.5 satisfies
(a) `F_J ≥ Ξ²` on `ℝ`;
(b) `F̂_J ≥ 0` on `[0, ∞)`; hence `F_J ∈ 𝒞_OPS ⊆ 𝒞`;
(c) `𝒜(F_J) = (1/π) Σ_{n ∈ PP, n > n_J} Λ(n) n^{-1/2} F̂_J(ξ_n)` (Lemma 2.3, Corollary 4.4, Proposition 4.5, no
hypothesis on the zeros), `𝒜(F_J) ≤ A_J` and `∫ F_J ≥ I_J` (the certified bounds of Table 1).
In (b) the paper's `F̂_J > 0` off the nodes, with zeros of order exactly two at the nodes, is formalised only as
`F̂_J ≥ 0` (the zeros of order at least two are `deriv_FT_Ffam_pp`); in (c) only the bounds used are stated. -/
theorem prop_exact_cone : ∀ row ∈ exactMembers,
    (∀ t : ℝ, (Xi t ^ 2).re ≤ (Ffam row.J t).re) ∧
    (∀ ξ : ℝ, 0 ≤ ξ → 0 ≤ FT (Ffam row.J) ξ) ∧ Ffam row.J ∈ ConeOPS ∧ Ffam row.J ∈ Cone ∧
    ((Arch (Ffam row.J) : ℝ) : ℂ) = (1 / Real.pi : ℂ) * ∑' n : ℕ,
      (if ppNth row.J < n then
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (Ffam row.J) (xiOf n)
      else 0) ∧
    Arch (Ffam row.J) ≤ (row.archUp : ℝ) ∧ (row.intLo : ℝ) ≤ intR (Ffam row.J) := by
  intro row hrow
  obtain ⟨hge, hOPS, hcone, hA, hI⟩ := exact_cone_facts row hrow
  exact ⟨hge, fun ξ _ => hOPS.2.2 ξ, hOPS, hcone,
    Arch_Ffam_tail (cert_finiteJ _ (exactMembers_J hrow)).1, hA, hI⟩

/-! ## Theorem 5.1 (v1.2) -/

/-- The rows of Table 1: `F_J ∈ 𝒞_OPS ⊆ 𝒞`, `∫ F_J > 0`, `𝒜(F_J) ≤ κ_J ∫ F_J`, and `κ* ≤ κ*_OPS ≤ κ_J`
(`κ_J ≥ A_J/I_J` is checked here, in exact arithmetic). -/
theorem thm_5_1_rows : ∀ row ∈ exactMembers, Ffam row.J ∈ ConeOPS ∧ Ffam row.J ∈ Cone ∧
    0 < intR (Ffam row.J) ∧ Arch (Ffam row.J) ≤ (row.kappa : ℝ) * intR (Ffam row.J) ∧
    kappaStar ≤ ((row.kappa : ℝ) : EReal) ∧ kappaOPS ≤ ((row.kappa : ℝ) : EReal) := by
  intro row hrow
  obtain ⟨-, hOPS, hcone, hA, hI⟩ := exact_cone_facts row hrow
  -- the arithmetic of the rows: `0 < I`, `0 ≤ κ_J` and `A ≤ κ_J I`
  have harith : (0 : ℝ) < row.intLo ∧ (0 : ℝ) ≤ row.kappa ∧
      (row.archUp : ℝ) ≤ (row.kappa : ℝ) * row.intLo := by
    simp only [exactMembers, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨hI0, hk0, hAI⟩ := harith
  have hpos : 0 < intR (Ffam row.J) := hI0.trans_le hI
  have hA' : Arch (Ffam row.J) ≤ (row.kappa : ℝ) * intR (Ffam row.J) :=
    hA.trans (hAI.trans (mul_le_mul_of_nonneg_left hI hk0))
  have hdiv : Arch (Ffam row.J) / intR (Ffam row.J) ≤ (row.kappa : ℝ) := by
    rw [div_le_iff₀ hpos]; exact hA'
  have hOPSle : kappaOPS ≤ ((row.kappa : ℝ) : EReal) :=
    (slack_le homog_Arch scalable_ConeOPS_Arch hOPS hpos).trans (by exact_mod_cast hdiv)
  exact ⟨hOPS, hcone, hpos, hA', kappaStar_le_kappaOPS.trans hOPSle, hOPSle⟩

theorem row111_mem :
    (⟨111, 398510732132 / 10 ^ 1071, 2788431830818955391538 / 10 ^ 21, kappa111⟩ : ExactRow) ∈
      exactMembers := by
  simp [exactMembers, kappa111]

/-- **Theorem 5.1 (v1.2).**  `κ* ≤ κ*_OPS ≤ 1.4291572 · 10^{-1060}`.  More precisely, for each `J` in Table 1
(`exactMembers`: `J = 10, 60, 61, 110, 111`) the exact member `F_J = Ξ² P_J(t²)` lies in `𝒞_OPS ⊆ 𝒞`, has
`∫ F_J > 0` and satisfies `𝒜(F_J)/∫ F_J ≤ κ_J`, so `κ* ≤ κ*_OPS ≤ κ_J`; in particular
`κ₁₁₁ = 1.4291572 · 10^{-1060}` (and `κ₁₁₀ = 2.0010115 · 10^{-1042}`). -/
theorem thm_5_1 :
    (kappaStar ≤ kappaOPS ∧ kappaOPS ≤ ((kappa111 : ℝ) : EReal)) ∧
    ∀ row ∈ exactMembers, Ffam row.J ∈ ConeOPS ∧ Ffam row.J ∈ Cone ∧ 0 < intR (Ffam row.J) ∧
      Arch (Ffam row.J) ≤ (row.kappa : ℝ) * intR (Ffam row.J) ∧
      kappaStar ≤ ((row.kappa : ℝ) : EReal) ∧ kappaOPS ≤ ((row.kappa : ℝ) : EReal) :=
  ⟨⟨kappaStar_le_kappaOPS, (thm_5_1_rows _ row111_mem).2.2.2.2.2⟩, thm_5_1_rows⟩

/-- The certified facts about `F₁₁₁`: `F₁₁₁ ∈ 𝒞`, `∫ F₁₁₁ > 0`, `𝒜(F₁₁₁) ≤ κ₁₁₁ ∫ F₁₁₁`, `κ* ≤ κ₁₁₁`,
`κ*_OPS ≤ κ₁₁₁`, and `𝒜(F₁₁₁) ≤ 3.98510732132 · 10^{-1060}`. -/
theorem exact111 : Ffam 111 ∈ Cone ∧ 0 < intR (Ffam 111) ∧
    Arch (Ffam 111) ≤ (kappa111 : ℝ) * intR (Ffam 111) ∧ kappaStar ≤ ((kappa111 : ℝ) : EReal) ∧
    kappaOPS ≤ ((kappa111 : ℝ) : EReal) ∧ Arch (Ffam 111) ≤ (398510732132 : ℝ) / 10 ^ 1071 := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := thm_5_1_rows _ row111_mem
  have h6 := (exact_cone_facts _ row111_mem).2.2.2.1
  refine ⟨h1, h2, h3, h4, h5, h6.trans_eq ?_⟩
  norm_num

/-- **Theorem 5.1 (v1.2), in particular.** `κ* ≤ 1.4291572 · 10^{-1060}` (the exact member `F₁₁₁`). -/
theorem kappaStar_le_kappa111 : kappaStar ≤ ((kappa111 : ℝ) : EReal) := exact111.2.2.2.1

/-- **Theorem 5.1 (v1.2), in particular.** `κ*_OPS ≤ 1.4291572 · 10^{-1060}` (`F₁₁₁ ∈ 𝒞_OPS`). -/
theorem kappaOPS_le_kappa111 : kappaOPS ≤ ((kappa111 : ℝ) : EReal) := exact111.2.2.2.2.1

/-- The normalised exact member `F₁₁₁/∫F₁₁₁`. -/
theorem exists_cert111 : ∃ F ∈ Cone, intR F = 1 ∧ Arch F ≤ (kappa111 : ℝ) := by
  obtain ⟨hcone, hpos, hA, -⟩ := exact111
  obtain ⟨h1, h2, h3⟩ := normalize homog_Arch (scalable_ConeG_Arch xi2) hcone hpos
  refine ⟨_, h1, h2, ?_⟩
  rw [h3, div_le_iff₀ hpos]
  exact hA

theorem two_pi_kappa111 : 2 * Real.pi * (kappa111 : ℝ) ≤ (89796596 : ℝ) / 10 ^ 1067 := by
  have hpi := Real.pi_lt_d20
  unfold kappa111
  push_cast
  set x : ℝ := 14291572 / 10 ^ 1067 with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1 : (89796596 : ℝ) / 10 ^ 1067 = (89796596 / 14291572 : ℝ) * x := by
    rw [hx]; field_simp
  have h2 : 2 * Real.pi ≤ (89796596 / 14291572 : ℝ) := by
    have : (2 : ℝ) * 3.14159265358979323847 ≤ 89796596 / 14291572 := by norm_num
    linarith
  rw [h1]
  exact mul_le_mul_of_nonneg_right h2 hx0.le

/-! ## Corollary 5.2 (v1.2) -/

/-- **Corollary 5.2 (v1.2).**
(a) No admissible pair has a zero measure `μ ≥ λ dt` with `λ > 1.4291572 · 10^{-1060}`.
(b) If `log q < −2π · 1.4291572 · 10^{-1060}`, in particular if `0 < q ≤ 1 − 8.98 · 10^{-1060}`, the data `𝒜_q`
admit no admissible pair; equivalently, replacing `log π` by `log π + η` in `Ω_∞` (that is, `log q = −η`) leaves
no admissible pair once `η > 8.9796596 · 10^{-1060}`.  Hence `q_min = e^{−2πκ*} ≥ 1 − 8.98 · 10^{-1060}`, and the
classical conductor bound optimised over `𝒞_OPS`, `e^{−2πκ*_OPS}`, is at least `1 − 8.98 · 10^{-1060}` too; under
RH, `1 − 8.98 · 10^{-1060} ≤ q_min ≤ 1` (`cor_5_2_RH`).  (Lemma 2.5 for `F₁₁₁/∫F₁₁₁`, Theorem 5.1.) -/
theorem cor_5_2 :
    (∀ p ∈ K, ∀ lam : ℝ, (kappa111 : ℝ) < lam → ¬ DominatesLeb p.μ lam) ∧
    (∀ q : ℝ, 0 < q → Real.log q < -2 * Real.pi * (kappa111 : ℝ) → Kset (Arch_q q) xi2 = ∅) ∧
    (∀ q : ℝ, 0 < q → q ≤ 1 - (898 : ℝ) / 10 ^ 1062 → Kset (Arch_q q) xi2 = ∅) ∧
    (∀ η : ℝ, (89796596 : ℝ) / 10 ^ 1067 < η →
      Kset (ArchShift (-η / (2 * Real.pi))) xi2 = ∅) ∧
    1 - (898 : ℝ) / 10 ^ 1062 ≤ qmin ∧ 1 - (898 : ℝ) / 10 ^ 1062 ≤ qminOPS := by
  obtain ⟨F, hF, h1, hA⟩ := exists_cert111
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the key: an admissible pair for `𝒜 + λ∫` forces `λ ≥ −κ₁₁₁`
  have key : ∀ lam : ℝ, (Kset (ArchShift lam) xi2).Nonempty → -(kappa111 : ℝ) ≤ lam := by
    rintro lam ⟨p, hp⟩
    have := weak_duality_nonneg hp hF
    simp only [ArchShift, h1, mul_one] at this
    linarith
  have hb : ∀ q : ℝ, 0 < q → Real.log q < -2 * Real.pi * (kappa111 : ℝ) →
      Kset (Arch_q q) xi2 = ∅ := by
    intro q _ hlog
    by_contra hne
    have := key _ (Set.nonempty_iff_ne_empty.mpr hne)
    have h2 : -(kappa111 : ℝ) * (2 * Real.pi) ≤ Real.log q := by
      rw [le_div_iff₀ (by positivity)] at this; exact this
    nlinarith
  refine ⟨fun p hp lam hlam => not_dominatesLeb_of_cone hp hF h1 (lt_of_le_of_lt hA hlam),
    hb, ?_, ?_, ?_, ?_⟩
  · intro q hq hq'
    apply hb q hq
    have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq
    have := two_pi_kappa111
    have : (89796596 : ℝ) / 10 ^ 1067 < (898 : ℝ) / 10 ^ 1062 := by norm_num
    nlinarith
  · intro η hη
    by_contra hne
    have := key _ (Set.nonempty_iff_ne_empty.mpr hne)
    have h2 : η ≤ (kappa111 : ℝ) * (2 * Real.pi) := by
      have h3 : -(kappa111 : ℝ) ≤ -η / (2 * Real.pi) := this
      rw [le_div_iff₀ (by positivity)] at h3
      linarith
    have := two_pi_kappa111
    nlinarith
  · -- `q_min = e^{−2πκ*} ≥ e^{−2πκ₁₁₁} ≥ 1 − 2πκ₁₁₁ ≥ 1 − 8.98·10^{-1060}`
    have hk : kappaStar.toReal ≤ (kappa111 : ℝ) := by
      have := kappaStar_le_kappa111
      rw [← kappaStar_coe] at this
      exact_mod_cast this
    unfold qmin
    have h2 := Real.add_one_le_exp (-2 * Real.pi * kappaStar.toReal)
    have := two_pi_kappa111
    have : (89796596 : ℝ) / 10 ^ 1067 < (898 : ℝ) / 10 ^ 1062 := by norm_num
    nlinarith
  · -- the same for `e^{−2πκ*_OPS}`
    have hk : kappaOPS.toReal ≤ (kappa111 : ℝ) := by
      have := kappaOPS_le_kappa111
      rw [← EReal.coe_toReal kappaOPS_ne_top kappaOPS_ne_bot] at this
      exact_mod_cast this
    unfold qminOPS
    have h2 := Real.add_one_le_exp (-2 * Real.pi * kappaOPS.toReal)
    have := two_pi_kappa111
    have : (89796596 : ℝ) / 10 ^ 1067 < (898 : ℝ) / 10 ^ 1062 := by norm_num
    nlinarith

/-- **Corollary 5.2, last clause (v1.2).** Under RH, `1 − 8.98 · 10^{-1060} ≤ q_min ≤ 1`. -/
theorem cor_5_2_RH (hRH : RiemannHypothesis) : 1 - (898 : ℝ) / 10 ^ 1062 ≤ qmin ∧ qmin ≤ 1 := by
  refine ⟨cor_5_2.2.2.2.2.1, ?_⟩
  have h0 : 0 ≤ kappaStar := condE_iff_kappaStar_nonneg.mp ?_
  · unfold qmin
    rw [Real.exp_le_one_iff]
    have : 0 ≤ kappaStar.toReal := EReal.toReal_nonneg h0
    nlinarith [Real.pi_pos]
  · exact ⟨_, (pZeta_mem_K_of_RH hRH)⟩

/-! ## The facts about `F₁₁₁` used by Corollary 5.3 -/

/-- The exact member `F₁₁₁` for Corollary 5.3: `F₁₁₁ ∈ 𝒞`, `F₁₁₁ ≥ Ξ²` on `ℝ` (`P₁₁₁(0) = 1` and every
coefficient of `P₁₁₁` is positive, Proposition 5.6), and `𝒜(F₁₁₁) ≤ 3.98510732132 · 10^{-1060} ≤ 3.99 · 10^{-1060}`. -/
theorem exact111_near_rigidity : Ffam 111 ∈ Cone ∧ (∀ t : ℝ, (Xi t ^ 2).re ≤ (Ffam 111 t).re) ∧
    Arch (Ffam 111) ≤ (399 : ℝ) / 10 ^ 1062 := by
  obtain ⟨hcone, -, -, -, -, hA⟩ := exact111
  exact ⟨hcone, Ffam_ge_Xi_sq (pcoef_nonneg_of_finiteJ (by simp)), hA.trans (by norm_num)⟩

end PosRig
