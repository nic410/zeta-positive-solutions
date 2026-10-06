/-
Facts about `ζ`, `ξ`, `Ξ`, the zeros and their multiplicities, from Mathlib (and, where marked,
built modules of Zeta23, or the ledger axiom `riemannZeta_half_neg`).
-/
import PositivityRigidity.Ledger
import Zeta23.Statement.Seam
import Zeta23.ZetaReflect

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-- `ζ(1/2) < 0` (the case `σ = 1/2` of the ledger axiom `riemannZeta_neg_of_mem_Ioo`). -/
theorem riemannZeta_half_neg : riemannZeta (1 / 2) < 0 := by
  have h := riemannZeta_neg_of_mem_Ioo (1 / 2) (by norm_num) (by norm_num)
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  rwa [e] at h

/-- `Γ_ℝ(s̄) = conj Γ_ℝ(s)` (as in Zeta23's `RvM.Gammaℝ_conj`). -/
theorem Gammaℝ_conj' (s : ℂ) :
    Complex.Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Complex.Gammaℝ s) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : ∀ w : ℂ, (Real.pi : ℂ) ^ ((starRingEnd ℂ) w) = (starRingEnd ℂ) ((Real.pi : ℂ) ^ w) := by
    intro w
    rw [cpow_def_of_ne_zero hpi, cpow_def_of_ne_zero hpi, ← Complex.exp_conj, map_mul,
      ← Complex.ofReal_log Real.pi_pos.le, Complex.conj_ofReal]
  have h1 : -((starRingEnd ℂ) s) / 2 = (starRingEnd ℂ) (-s / 2) := by
    simp [map_div₀, map_neg, map_ofNat]
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    simp [map_div₀, map_ofNat]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, h1, h2, hc, Complex.Gamma_conj, map_mul]

/-- `ξ(s) = ½ s(s−1) Γ_ℝ(s) ζ(s)` for `s ≠ 1` with `Γ_ℝ(s) ≠ 0` (i.e. `s ∉ {0, −2, −4, …}`):
`xiR` is Riemann's `ξ`.  (At `s = −2n`, `n ≥ 1`, Mathlib's `Γ_ℝ` takes the junk value `0`, so the
hypothesis `Γ_ℝ(s) ≠ 0` cannot be weakened to `s ≠ 0`.) -/
theorem xiR_eq {s : ℂ} (h0 : Complex.Gammaℝ s ≠ 0) (h1 : s ≠ 1) :
    xiR s = s * (s - 1) / 2 * Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact h0 (Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩)
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  unfold xiR
  field_simp
  ring

theorem differentiable_xiR : Differentiable ℂ xiR := by
  unfold xiR
  exact ((((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2)

theorem differentiable_Xi : Differentiable ℂ Xi := by
  unfold Xi
  exact differentiable_xiR.comp ((differentiable_const _).add
    ((differentiable_const _).mul differentiable_id))

theorem xiR_one_sub (s : ℂ) : xiR (1 - s) = xiR s := by
  unfold xiR
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem Xi_even (z : ℂ) : Xi (-z) = Xi z := by
  unfold Xi
  rw [← xiR_one_sub (1 / 2 + I * z)]
  congr 1
  ring

/-- On the critical line, `conj ξ(s) = ξ(s̄)`. -/
private theorem conj_xiR_crit (t : ℝ) :
    (starRingEnd ℂ) (xiR (1 / 2 + I * (t : ℂ))) = xiR ((starRingEnd ℂ) (1 / 2 + I * (t : ℂ))) := by
  set s : ℂ := 1 / 2 + I * (t : ℂ) with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hcre : ((starRingEnd ℂ) s).re = 1 / 2 := by rw [Complex.conj_re, hsre]
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hGc : Complex.Gammaℝ ((starRingEnd ℂ) s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hcre]; norm_num)
  have h1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    norm_num at this
  have h1c : (starRingEnd ℂ) s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hcre] at this
    norm_num at this
  rw [xiR_eq hG h1, xiR_eq hGc h1c, Gammaℝ_conj', riemannZeta_conj]
  simp only [map_mul, map_div₀, map_sub, map_one, map_ofNat]

/-- `Ξ` is real on `ℝ`. -/
theorem Xi_real (t : ℝ) : (Xi t).im = 0 := by
  have hconj : (starRingEnd ℂ) (Xi t) = Xi t := by
    unfold Xi
    rw [conj_xiR_crit t]
    have : (starRingEnd ℂ) (1 / 2 + I * (t : ℂ)) = 1 - (1 / 2 + I * (t : ℂ)) := by
      apply Complex.ext <;> norm_num
    rw [this, xiR_one_sub]
  exact Complex.conj_eq_iff_im.mp hconj

theorem Xi_eq_zero_iff (t : ℝ) : Xi t = 0 ↔ t ∈ Zzeta := by
  set s : ℂ := 1 / 2 + I * (t : ℂ) with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have h1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    norm_num at this
  have h0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    norm_num at this
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  show xiR s = 0 ↔ riemannZeta s = 0
  rw [xiR_eq hG h1]
  have hc : s * (s - 1) / 2 * Complex.Gammaℝ s ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero h0 hs1) two_ne_zero) hG
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    rw [h, mul_zero]

/-- `Ξ(t_ρ) = ξ(ρ) = 0` at every non-trivial zero, on or off the line (proof of Corollary 4.4). -/
theorem Xi_tOf {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : Xi (tOf ρ) = 0 := by
  obtain ⟨hz, hre0, hre1⟩ := hρ
  have harg : 1 / 2 + I * tOf ρ = ρ := by
    unfold tOf
    ring_nf
    rw [I_sq]
    ring
  have hG : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre0
  have h1 : ρ ≠ 1 := by
    intro h
    rw [h] at hre1
    simp at hre1
  unfold Xi
  rw [harg, xiR_eq hG h1, hz, mul_zero]

/-- `Γ_ℝ(1/2) = π^{-1/4} Γ(1/4)`, a positive real number. -/
private theorem Gammaℝ_half :
    Complex.Gammaℝ (1 / 2) = ((Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  have e1 : -(1 / 2 : ℂ) / 2 = ((-(1 / 4 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) / 2 = ((1 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal, ← Complex.ofReal_mul]

/-- `Ξ(0) = −(1/8) Γ_ℝ(1/2) ζ(1/2) > 0` (proof of Theorem 3.8), from `ζ(1/2) < 0`. -/
theorem Xi_zero_pos : 0 < (Xi 0).re := by
  have hG : Complex.Gammaℝ (1 / 2) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have h1 : (1 / 2 : ℂ) ≠ 1 := by norm_num
  have hX : Xi 0 = xiR (1 / 2) := by unfold Xi; congr 1; ring
  have hζ := riemannZeta_half_neg
  rw [Complex.lt_def] at hζ
  obtain ⟨hre, him⟩ := hζ
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  set g : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) with hg
  have hgpos : 0 < g := mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by norm_num))
  rw [hX, xiR_eq hG h1, Gammaℝ_half]
  have : ((1 / 2 : ℂ) * (1 / 2 - 1) / 2 * (g : ℂ) * riemannZeta (1 / 2)) =
      (((-(1 / 8 : ℝ)) * g : ℝ) : ℂ) * riemannZeta (1 / 2) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  have : 0 < -(1 / 8 : ℝ) * g * (riemannZeta (1 / 2)).re := by
    have h8 : -(1 / 8 : ℝ) * g < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg h8 hre
  exact this

/-- `0 ∉ Z_ζ` (`ζ(1/2) ≠ 0`, §3.1). -/
theorem zero_not_mem_Zzeta : (0 : ℝ) ∉ Zzeta := by
  intro h
  have h' : riemannZeta (1 / 2) = 0 := by
    have := h
    simp only [Zzeta, Set.mem_ofPred_eq, Complex.ofReal_zero, mul_zero, add_zero] at this
    exact this
  have hζ := riemannZeta_half_neg
  rw [h'] at hζ
  exact lt_irrefl _ hζ

private theorem conj_half_add (γ : ℝ) :
    (starRingEnd ℂ) (1 / 2 + I * (γ : ℂ)) = 1 / 2 + I * ((-γ : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

theorem neg_mem_Zzeta {γ : ℝ} : -γ ∈ Zzeta ↔ γ ∈ Zzeta := by
  simp only [Zzeta, Set.mem_ofPred_eq]
  rw [← conj_half_add, riemannZeta_conj, map_eq_zero]

theorem mult_neg (γ : ℝ) : mult (1 / 2 + I * ((-γ : ℝ) : ℂ)) = mult (1 / 2 + I * (γ : ℂ)) := by
  have hne : (1 / 2 + I * (γ : ℂ)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  unfold mult analyticOrderNatAt
  rw [← conj_half_add, Zeta23.analyticOrderAt_zeta_conj hne]

theorem one_le_mult {s : ℂ} (hs : riemannZeta s = 0) (h1 : s ≠ 1) : 1 ≤ mult s := by
  have han : AnalyticAt ℂ riemannZeta s := Zeta23.riemannZeta_analyticOnNhd_compl_one s h1
  have hne0 : analyticOrderAt riemannZeta s ≠ 0 := han.analyticOrderAt_ne_zero.mpr hs
  have hnetop := Zeta23.analyticOrderAt_riemannZeta_ne_top h1
  unfold mult analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

theorem tOf_half_add (γ : ℝ) : tOf (1 / 2 + I * (γ : ℂ)) = (γ : ℂ) := by
  unfold tOf
  ring_nf
  rw [I_sq]
  ring

theorem half_add_mem_NontrivialZeros {γ : ℝ} (h : γ ∈ Zzeta) :
    (1 / 2 + I * (γ : ℂ)) ∈ NontrivialZeros := by
  refine ⟨h, ?_, ?_⟩ <;> norm_num

/-- The non-trivial zeros form a countable set (finitely many in each window of height 1,
`Zeta23.ZetaSeam.finite_window_holds`). -/
theorem NontrivialZeros_countable : NontrivialZeros.Countable := by
  have hsub : NontrivialZeros ⊆ ⋃ n : ℤ, ({ρ | Zeta23.IsNontrivialZero ρ} ∩
      {ρ : ℂ | ((n : ℝ)) < ρ.im ∧ ρ.im ≤ (n : ℝ) + 1}) := by
    intro ρ hρ
    refine Set.mem_iUnion.mpr ⟨⌈ρ.im⌉ - 1, hρ, ?_, ?_⟩
    · push_cast
      linarith [Int.ceil_lt_add_one ρ.im]
    · push_cast
      linarith [Int.le_ceil ρ.im]
  refine Set.Countable.mono hsub (Set.countable_iUnion fun n => ?_)
  have := Zeta23.ZetaSeam.finite_window_holds (n : ℝ) ((n : ℝ) + 1)
  exact this.countable

theorem Zzeta_countable : Zzeta.Countable := by
  have hsub : Zzeta ⊆ (fun ρ : ℂ => ρ.im) '' NontrivialZeros := by
    intro γ hγ
    exact ⟨1 / 2 + I * (γ : ℂ), half_add_mem_NontrivialZeros hγ, by simp⟩
  exact (NontrivialZeros_countable.image _).mono hsub

/-- Under RH every non-trivial zero is on the critical line. -/
theorem re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ρ.re = 1 / 2 := by
  obtain ⟨hz, hre0, hre1⟩ := hρ
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hre0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    simp at hre1

end PosRig
