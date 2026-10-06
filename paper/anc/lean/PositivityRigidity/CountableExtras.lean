/-
v1.1: Theorem 3.8 (countably many extra zeros) and Theorem B(b), from the ledger axiom
`brs_countable_meanvalue` (Definition 3.4, Lemma 3.7 for countable `E`, Lemmas B.3–B.4) and Proposition 3.5 in
its signed form (`support_uniqueness_thm`).

* `cumulativeCond_of_weightedCond`: the weighted form of (3.5) implies the cumulative form (Mathlib only);
* `extra_zeros_countable`: Theorem 3.8 in atom-weight form (real measures), for every `(B, α)` with the
  properties of Definition 3.4, Lemma 3.7 and Lemma B.4;
* `extra_zeros_countable_admissible`: its last sentences (admissible pairs);
* `theoremB_b_countable`: Theorem B(b) (countable `E`, not necessarily symmetric, weighted condition);
* `theoremB_finite_of_countable`: the finite case (the statement of `theoremB'`) without the Landau step.
-/
import PositivityRigidity.Uniqueness
import PositivityRigidity.ExtrasDefs

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## The summability condition (3.5) -/

theorem partialMass_eq_tsum_indicator (S : Set ℝ) (β : ℝ → ℝ) (T : ℝ) :
    partialMass S β T = ∑' e, (S ∩ Set.Iic T).indicator (fun e => ENNReal.ofReal (β e)) e :=
  tsum_subtype (S ∩ Set.Iic T) (fun e => ENNReal.ofReal (β e))

theorem partialMass_mono {S S' : Set ℝ} {β β' : ℝ → ℝ} (hS : S ⊆ S')
    (hβ : ∀ e ∈ S, β e ≤ β' e) (T : ℝ) : partialMass S β T ≤ partialMass S' β' T := by
  rw [partialMass_eq_tsum_indicator, partialMass_eq_tsum_indicator]
  refine ENNReal.tsum_le_tsum fun e => ?_
  by_cases he : e ∈ S ∩ Set.Iic T
  · have he' : e ∈ S' ∩ Set.Iic T := ⟨hS he.1, he.2⟩
    rw [Set.indicator_of_mem he, Set.indicator_of_mem he']
    exact ENNReal.ofReal_le_ofReal (hβ e he.1)
  · rw [Set.indicator_of_notMem he]
    exact zero_le

theorem SqrtSmall.mono {S S' : Set ℝ} {β β' : ℝ → ℝ} (h : SqrtSmall S' β') (hS : S ⊆ S')
    (hβ : ∀ e ∈ S, β e ≤ β' e) : SqrtSmall S β := fun ε hε =>
  (h ε hε).mono fun T hT => (partialMass_mono hS hβ T).trans hT

/-- Bounded partial sums are `o(√T)`. -/
theorem sqrtSmall_of_bounded {S : Set ℝ} {β : ℝ → ℝ} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ T, partialMass S β T ≤ C) : SqrtSmall S β := by
  intro ε hε
  have hev : ∀ᶠ T in atTop, C.toReal ≤ ε * Real.sqrt T :=
    (Real.tendsto_sqrt_atTop.const_mul_atTop hε).eventually_ge_atTop C.toReal
  filter_upwards [hev] with T hT
  calc partialMass S β T ≤ C := h T
    _ = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
    _ ≤ ENNReal.ofReal (ε * Real.sqrt T) := ENNReal.ofReal_le_ofReal hT

/-- A finite set satisfies every `o(√T)` condition. -/
theorem sqrtSmall_of_finite {S : Set ℝ} (hS : S.Finite) (β : ℝ → ℝ) : SqrtSmall S β := by
  refine sqrtSmall_of_bounded (C := ∑ e ∈ hS.toFinset, ENNReal.ofReal (β e))
    (ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top) fun T => ?_
  rw [partialMass_eq_tsum_indicator]
  calc ∑' e, (S ∩ Set.Iic T).indicator (fun e => ENNReal.ofReal (β e)) e
      ≤ ∑' e, S.indicator (fun e => ENNReal.ofReal (β e)) e :=
        ENNReal.tsum_le_tsum fun e => Set.indicator_le_indicator_of_subset Set.inter_subset_left
          (fun _ => zero_le) e
    _ = ∑ e ∈ hS.toFinset, S.indicator (fun e => ENNReal.ofReal (β e)) e :=
        tsum_eq_sum fun e he => Set.indicator_of_notMem (by simpa using he) _
    _ = ∑ e ∈ hS.toFinset, ENNReal.ofReal (β e) :=
        Finset.sum_congr rfl fun e he => Set.indicator_of_mem (by simpa using he) _

/-- **The weighted form of (3.5) implies the cumulative form** (Appendix B.1.6, after (B.7)): if
`Σ_{e ∈ E, e > 0} b_e (1 + e)^{-1/2} < ∞` then `Σ_{e ∈ E, 0 < e ≤ T} b_e = o(T^{1/2})`. -/
theorem cumulativeCond_of_weightedCond {E : Set ℝ} {w : ℝ → ℝ} (h : WeightedCond E w) :
    CumulativeCond E w := by
  intro ε hε
  set S : Set ℝ := E ∩ Set.Ioi 0 with hSdef
  set b : ℝ → ℝ := zetaWeight w with hbdef
  have hb0 : ∀ e, 0 ≤ b e := fun e => by rw [hbdef]; unfold zetaWeight; positivity
  set g : ℝ → ℝ≥0∞ := S.indicator (fun e => ENNReal.ofReal (b e / Real.sqrt (1 + e))) with hgdef
  have hg : ∑' e, g e ≠ ⊤ := by
    rw [hgdef, ← tsum_subtype]
    exact h
  -- a finite set outside of which the weighted sum is `< ε/4`
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero hg
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨s, hs⟩ := (htail.eventually (gt_mem_nhds hpos)).exists
  set C : ℝ := ∑ e ∈ s, b e with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun e _ => hb0 e
  filter_upwards [eventually_ge_atTop (max 1 ((2 * C / ε) ^ 2))] with T hT
  have hT1 : 1 ≤ T := le_of_max_le_left hT
  have hT2 : (2 * C / ε) ^ 2 ≤ T := le_of_max_le_right hT
  -- pointwise bound
  have hpt : ∀ e, (S ∩ Set.Iic T).indicator (fun e => ENNReal.ofReal (b e)) e ≤
      (↑s : Set ℝ).indicator (fun e => ENNReal.ofReal (b e)) e +
        ENNReal.ofReal (Real.sqrt (1 + T)) * (↑s : Set ℝ)ᶜ.indicator g e := by
    intro e
    by_cases he : e ∈ S ∩ Set.Iic T
    · rw [Set.indicator_of_mem he]
      by_cases hes : e ∈ (↑s : Set ℝ)
      · rw [Set.indicator_of_mem hes]
        exact le_add_right le_rfl
      · rw [Set.indicator_of_mem (show e ∈ (↑s : Set ℝ)ᶜ from hes), hgdef,
          Set.indicator_of_mem he.1, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
        have he0 : 0 < e := he.1.2
        have heT : e ≤ T := he.2
        have hs1 : 0 < Real.sqrt (1 + e) := Real.sqrt_pos.mpr (by linarith)
        have hs2 : Real.sqrt (1 + e) ≤ Real.sqrt (1 + T) := Real.sqrt_le_sqrt (by linarith)
        rw [mul_div_assoc', le_div_iff₀ hs1]
        exact mul_le_mul_of_nonneg_left hs2 (hb0 e) |>.trans_eq (mul_comm _ _)
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  have hsum1 : ∑' e, (↑s : Set ℝ).indicator (fun e => ENNReal.ofReal (b e)) e = ENNReal.ofReal C := by
    rw [tsum_eq_sum (s := s) fun e he => Set.indicator_of_notMem (by simpa using he) _,
      Finset.sum_congr rfl fun e he => Set.indicator_of_mem (by simpa using he) _, hCdef,
      ENNReal.ofReal_sum_of_nonneg fun e _ => hb0 e]
  have hsum2 : ∑' e, (↑s : Set ℝ)ᶜ.indicator g e < ENNReal.ofReal (ε / 4) := by
    rw [← tsum_subtype]
    exact hs
  -- the real inequality `C + √(1+T) ε/4 ≤ ε √T`
  have hsqrtT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have h1 : Real.sqrt (1 + T) ≤ 2 * Real.sqrt T := by
    rw [show 2 * Real.sqrt T = Real.sqrt (4 * T) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 2 * C / ε ≤ Real.sqrt T := by
    rw [← Real.sqrt_sq (show 0 ≤ 2 * C / ε by positivity)]
    exact Real.sqrt_le_sqrt hT2
  have h3 : C ≤ ε * Real.sqrt T / 2 := by
    rw [div_le_iff₀ hε] at h2
    linarith
  have hreal : C + Real.sqrt (1 + T) * (ε / 4) ≤ ε * Real.sqrt T := by nlinarith
  calc partialMass S b T
      = ∑' e, (S ∩ Set.Iic T).indicator (fun e => ENNReal.ofReal (b e)) e :=
        partialMass_eq_tsum_indicator S b T
    _ ≤ ∑' e, ((↑s : Set ℝ).indicator (fun e => ENNReal.ofReal (b e)) e +
          ENNReal.ofReal (Real.sqrt (1 + T)) * (↑s : Set ℝ)ᶜ.indicator g e) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal C + ENNReal.ofReal (Real.sqrt (1 + T)) *
          ∑' e, (↑s : Set ℝ)ᶜ.indicator g e := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hsum1]
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal (Real.sqrt (1 + T)) * ENNReal.ofReal (ε / 4) := by
        gcongr
    _ = ENNReal.ofReal (C + Real.sqrt (1 + T) * (ε / 4)) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_add hC0 (by positivity)]
    _ ≤ ENNReal.ofReal (ε * Real.sqrt T) := ENNReal.ofReal_le_ofReal hreal

/-- The weighted condition (3.5) holds for every finite set. -/
theorem weightedCond_of_finite {E : Set ℝ} (hE : E.Finite) (w : ℝ → ℝ) : WeightedCond E w := by
  have hS : (E ∩ Set.Ioi 0).Finite := hE.subset Set.inter_subset_left
  unfold WeightedCond
  rw [tsum_subtype (E ∩ Set.Ioi 0) (fun e => ENNReal.ofReal (zetaWeight w e / Real.sqrt (1 + e))),
    tsum_eq_sum (s := hS.toFinset) fun e he => Set.indicator_of_notMem (by simpa using he) _]
  refine ENNReal.sum_ne_top.mpr fun e _ => ?_
  by_cases h : e ∈ E ∩ Set.Ioi 0
  · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-! ## Summability of pairings with atomic measures -/

/-- If `f` is `μ`-integrable and `μ` is carried by a countable set, then `Σ_x μ({x}) f(x)` converges
absolutely. -/
theorem summable_of_integrable_carriedBy {μ : Measure ℝ} {S : Set ℝ} (hS : S.Countable)
    (hμ : CarriedBy μ S) {f : ℝ → ℂ} (hf : Integrable f μ) :
    Summable (fun x : ℝ => ((μ.real {x} : ℝ) : ℂ) * f x) := by
  have h1 : ∫⁻ x, ‖f x‖ₑ ∂μ = ∑' x : S, ‖f x‖ₑ * μ {(x : ℝ)} := by
    have hres := restrict_eq_self_of_carriedBy hμ
    calc ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x in S, ‖f x‖ₑ ∂μ := by rw [hres]
      _ = ∑' x : S, ‖f x‖ₑ * μ {(x : ℝ)} := lintegral_countable _ hS
  have h2 : ∑' x : S, ‖f x‖ₑ * μ {(x : ℝ)} ≠ ⊤ := by
    rw [← h1]
    exact hf.2.ne
  have h3 : Summable (fun x : S => ‖((μ.real {(x : ℝ)} : ℝ) : ℂ) * f x‖) := by
    refine (ENNReal.summable_toReal h2).congr fun x => ?_
    rw [ENNReal.toReal_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg, measureReal_def, toReal_enorm, mul_comm]
  have h4 : Summable (fun x : S => ((μ.real {(x : ℝ)} : ℝ) : ℂ) * f x) := h3.of_norm
  have hsupp : Function.support (fun x : ℝ => ((μ.real {x} : ℝ) : ℂ) * f x) ⊆ S := by
    intro x hx
    by_contra hxS
    apply hx
    have hx0 : μ {x} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hxS) hμ
    simp [measureReal_def, hx0]
  rw [← Set.indicator_eq_self.mpr hsupp]
  exact summable_subtype_iff_indicator.mp h4

/-! ## Theorem 3.8 -/

/-- **Theorem 3.8 (countably many extra zeros)**, in atom-weight form.  Let `B` be a basis with the
properties of Definition 3.4 and `α` a coefficient function for which Lemma 3.7 (countable `E`) and the
mean-value step (Lemmas B.3, B.4) hold.  Let `E ⊂ ℝ \ Z_ζ` be countable and symmetric, `μ = Σ w(x)δ_x` an
even real measure carried by `Z_ζ ∪ E` and `ν = Σ ν_m δ_{log m/4π}` a real measure carried by `ℳ` with
`𝒜(F) = ∫ F dμ + (1/π)∫ F̂ dν`, with absolutely convergent integrals, for every BRS function `F`.  Assume
`ν({log m/4π}) ≥ 0` for `m ≡ 2 (mod 3)`, `μ({0}) ≥ 0` if `0 ∈ E`, and (3.5) (weighted or cumulative).  Then
RH holds, `μ = μ_ζ` and `ν = ν_ζ`. -/
theorem extra_zeros_countable {B : BRSBasis} {α : ℕ → ℂ → ℂ} (hB : IsBRSBasis B)
    (h37 : Lemma36Count B α) (hMV : MeanValueStep α) {E : Set ℝ} (hEc : E.Countable)
    (hEZ : ∀ e ∈ E, e ∉ Zzeta) (hsymm : ∀ e ∈ E, -e ∈ E)
    (w : ℝ → ℝ) (ν : ℕ → ℝ) (heven : ∀ x, w (-x) = w x)
    (hsupp : ∀ x, w x ≠ 0 → x ∈ Zzeta ∨ x ∈ E)
    (hsumU : ∀ m : ℕ, 1 ≤ m → Summable (fun x : ℝ => (w x : ℂ) * B.U m x))
    (hsumV : ∀ v : VIndex, Summable (fun x : ℝ => (w x : ℂ) * B.V v x))
    (hid : BRSIdentity B w ν)
    (hpos : ∀ m : ℕ, m % 3 = 2 → 0 ≤ ν m) (h0 : (0 : ℝ) ∈ E → 0 ≤ w 0)
    (hsum : WeightedCond E w ∨ CumulativeCond E w) :
    RiemannHypothesis ∧ (∀ x, x ∉ Zzeta → w x = 0) ∧
      (∀ γ ∈ Zzeta, w γ = mult (1 / 2 + I * (γ : ℂ))) ∧ ∀ m : ℕ, 1 ≤ m → ν m = nuZetaAtom m := by
  have hcum : CumulativeCond E w := hsum.elim cumulativeCond_of_weightedCond id
  have h34 := h37 E hEc hEZ hsymm w ν heven hsupp hsumU hsumV hid
  set Ep : Set ℝ := E ∩ Set.Ici 0 with hEp
  -- positivity on the class `2 mod 3` gives `c_N(E) ≥ 0` there (Lemma 3.7)
  have hc : ∀ N : ℕ, N % 3 = 2 →
      Summable (fun e : ↥Ep => (rhoTilde w e : ℂ) * α N (sOf e)) ∧ 0 ≤ cNc α Ep w N := by
    intro N hN
    obtain ⟨hs, h⟩ := h34 N (by omega)
    rw [sqInd_of_mod3 hN, mul_zero, Complex.ofReal_zero, add_zero] at h
    exact ⟨hs, h ▸ Complex.zero_le_real.mpr (CN_nonneg_of_mod3 hpos hN)⟩
  -- (3.5) for `E₊`
  have hcumEp : CumulativeCond Ep w := by
    have hset : Ep ∩ Set.Ioi 0 = E ∩ Set.Ioi 0 := by
      ext x
      simp only [hEp, Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2⟩
    unfold CumulativeCond
    rw [hset]
    exact hcum
  -- the mean-value step (Lemma B.4)
  have hzero := hMV Ep (hEc.mono Set.inter_subset_left) Set.inter_subset_right w hcumEp
    (fun h => h0 h.1) hc
  -- hence no extra atoms
  have hwE : ∀ e ∈ E, w e = 0 := by
    have hpos' : ∀ e ∈ E, 0 ≤ e → w e = 0 := by
      intro e he hge
      have hr := hzero e ⟨he, hge⟩
      unfold rhoTilde at hr
      by_cases he0 : e = 0
      · subst he0
        rw [if_pos rfl] at hr
        have := Xi_zero_pos
        have : (2 : ℝ) * (Xi 0).re ≠ 0 := by positivity
        have h2 : w 0 * (2 * (Xi 0).re) = 0 := by linarith
        exact (mul_eq_zero.mp h2).resolve_right this
      · rw [if_neg he0] at hr
        have hXi : (Xi e).re ≠ 0 := by
          intro hre
          have : Xi e = 0 := Complex.ext (by simpa using hre) (by simpa using Xi_real e)
          exact hEZ e he ((Xi_eq_zero_iff e).mp this)
        have hden : (1 / 4 + e ^ 2 : ℝ) ≠ 0 := by positivity
        rw [div_eq_zero_iff] at hr
        rcases hr with hr | hr
        · exact (mul_eq_zero.mp hr).resolve_right hXi
        · exact absurd hr hden
    intro e he
    rcases le_or_gt 0 e with hge | hlt
    · exact hpos' e he hge
    · have := hpos' (-e) (hsymm e he) (by linarith)
      rw [← heven e]
      exact this
  have hsupp' : ∀ x, w x ≠ 0 → x ∈ Zzeta := by
    intro x hx
    rcases hsupp x hx with h | h
    · exact h
    · exact absurd (hwE x h) hx
  -- Proposition 3.5 in its signed form
  obtain ⟨hRH, hw, hν⟩ := support_uniqueness_thm hB w ν heven hsupp' hid
  refine ⟨hRH, fun x hx => ?_, hw, hν⟩
  by_contra hne
  exact hx (hsupp' x hne)

/-- **Theorem 3.8, last sentences (admissible pairs).**  Let `E ⊂ ℝ \ Z_ζ` be countable and symmetric.
Every admissible pair carried by `(Z_ζ ∪ E) × ℳ` whose zero measure satisfies (3.5), with
`a_e = μ({e})`, is `p_ζ`, and RH holds. -/
theorem extra_zeros_countable_admissible {E : Set ℝ} (hEc : E.Countable) (hEZ : Disjoint E Zzeta)
    (hsymm : ∀ e ∈ E, -e ∈ E) {p : Pair} (hp : p ∈ K) (hμ : CarriedBy p.μ (Zzeta ∪ E))
    (hν : CarriedBy p.ν BRSNodes)
    (hsum : WeightedCond E (fun x => p.μ.real {x}) ∨ CumulativeCond E (fun x => p.μ.real {x})) :
    RiemannHypothesis ∧ p = pZeta := by
  obtain ⟨hlfμ, hlfν⟩ := Admissible.isLocallyFinite hp
  have hfinμ : ∀ x : ℝ, p.μ {x} ≠ ⊤ := fun x => (isCompact_singleton.measure_lt_top).ne
  have hfinν : ∀ x : ℝ, p.ν {x} ≠ ⊤ := fun x => (isCompact_singleton.measure_lt_top).ne
  have hScount : (Zzeta ∪ E).Countable := Zzeta_countable.union hEc
  set w : ℝ → ℝ := fun x => p.μ.real {x} with hw
  set ν' : ℕ → ℝ := fun m => p.ν.real {brsNode m} with hν'
  obtain ⟨B, α, hB, h37, hMV⟩ := brs_countable_meanvalue
  obtain ⟨-, hU, hV, -, -, -, -⟩ := id hB
  -- the identity on the BRS functions, in atom-weight form, and absolute convergence of the pairings
  have hpair : ∀ F : ℂ → ℂ, rePart F ∈ TestClass → imPart F ∈ TestClass →
      ArchC F = pairAtoms w F + (1 / Real.pi : ℂ) * pairNodes ν' (FT F) ∧
        Summable (fun x : ℝ => (w x : ℂ) * F x) := by
    intro F hre him
    obtain ⟨h1, h2, h3⟩ := admissible_identityC hp hre him
    have e1 := integral_eq_tsum_of_carriedBy hScount hμ h1
    have e2 := integral_eq_tsum_brsNodes hν h2
    simp only [onR] at e1
    refine ⟨?_, summable_of_integrable_carriedBy hScount hμ h1⟩
    rw [h3, e1, e2]
    rfl
  have hid : BRSIdentity B w ν' :=
    ⟨fun m hm => (hpair _ (hU m hm).2.2.1 (hU m hm).2.2.2).1,
      fun v => (hpair _ (hV v).2.2.1 (hV v).2.2.2).1⟩
  have hsumU : ∀ m : ℕ, 1 ≤ m → Summable (fun x : ℝ => (w x : ℂ) * B.U m x) := fun m hm =>
    (hpair _ (hU m hm).2.2.1 (hU m hm).2.2.2).2
  have hsumV : ∀ v : VIndex, Summable (fun x : ℝ => (w x : ℂ) * B.V v x) := fun v =>
    (hpair _ (hV v).2.2.1 (hV v).2.2.2).2
  have heven : ∀ x, w (-x) = w x := by
    intro x
    simp only [hw, measureReal_def, EvenMeasure.singleton hp.1 x]
  have hsupp : ∀ x, w x ≠ 0 → x ∈ Zzeta ∨ x ∈ E := by
    intro x hx
    by_contra hnot
    apply hx
    have hx' : x ∉ Zzeta ∪ E := by
      simp only [Set.mem_union] at hnot ⊢; exact hnot
    have : p.μ {x} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hx') hμ
    simp [hw, measureReal_def, this]
  obtain ⟨hRH, hwoff, hwZ, hνZ⟩ := extra_zeros_countable hB h37 hMV hEc
    (fun e he => Set.disjoint_left.mp hEZ he) hsymm w ν' heven hsupp hsumU hsumV hid
    (fun m _ => measureReal_nonneg) (fun _ => measureReal_nonneg) hsum
  refine ⟨hRH, ?_⟩
  have hμeq : p.μ = muZeta := by
    refine measure_eq_of_carriedBy hScount hμ
      (measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left) muZeta_carriedBy) ?_
    intro x hx
    by_cases hxZ : x ∈ Zzeta
    · rw [muZeta_singleton hxZ, ← ENNReal.ofReal_toReal (hfinμ x)]
      have := hwZ x hxZ
      simp only [hw, measureReal_def] at this
      rw [this, ENNReal.ofReal_natCast]
    · have h1 : p.μ {x} = 0 := by
        have := hwoff x hxZ
        simp only [hw, measureReal_def] at this
        exact (ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right (hfinμ x)
      have h2 : muZeta {x} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.mpr hxZ) muZeta_carriedBy
      rw [h1, h2]
  have hνeq : p.ν = nuZeta := by
    refine measure_eq_of_carriedBy BRSNodes_countable hν nuZeta_carriedBy_BRSNodes ?_
    rintro x ⟨m, hm, rfl⟩
    rw [nuZeta_singleton_brsNode hm, ← ENNReal.ofReal_toReal (hfinν _)]
    have := hνZ m hm
    simp only [hν', measureReal_def] at this
    rw [this]
  cases p
  simp only at hμeq hνeq
  rw [hμeq, hνeq]
  rfl

/-! ## Theorem B(b) and the finite case -/

/-- **Theorem B(b) (v1.1).**  Let `E ⊂ ℝ \ Z_ζ` be countable.  If `(μ, ν) ∈ 𝒦`, `μ` is carried by `Z_ζ ∪ E`,
`ν` is carried by `ℳ`, and `Σ_{e ∈ E, e > 0} μ({e}) |ζ(1/2 + ie)| (1 + e)^{-1/2} < ∞`, then RH holds and
`(μ, ν) = p_ζ`.  (Theorem 3.8 for `E ∪ (−E)`.) -/
theorem theoremB_b_countable {E : Set ℝ} (hEc : E.Countable) (hEZ : Disjoint E Zzeta) {p : Pair}
    (hp : p ∈ K) (hμ : CarriedBy p.μ (Zzeta ∪ E)) (hν : CarriedBy p.ν BRSNodes)
    (hsum : WeightedCond E (fun x => p.μ.real {x})) : RiemannHypothesis ∧ p = pZeta := by
  set E' : Set ℝ := E ∪ (fun x => -x) '' E with hE'
  have hE'c : E'.Countable := hEc.union (hEc.image _)
  have hE'Z : Disjoint E' Zzeta := by
    rw [hE', Set.disjoint_union_left]
    refine ⟨hEZ, Set.disjoint_left.mpr ?_⟩
    rintro x ⟨e, he, rfl⟩ hx
    exact Set.disjoint_left.mp hEZ he (neg_mem_Zzeta.mp hx)
  have hsymm : ∀ e ∈ E', -e ∈ E' := by
    rintro e (he | ⟨e', he', rfl⟩)
    · exact Or.inr ⟨e, he, rfl⟩
    · left; simpa using he'
  have hμ' : CarriedBy p.μ (Zzeta ∪ E') :=
    measure_mono_null (Set.compl_subset_compl.mpr
      (Set.union_subset_union_right _ Set.subset_union_left)) hμ
  -- the weighted sum over `E'₊` has no more terms than over `E₊`: the new atoms vanish
  have hsum' : WeightedCond E' (fun x => p.μ.real {x}) := by
    have hle : ∑' e : ↥(E' ∩ Set.Ioi 0),
        ENNReal.ofReal (zetaWeight (fun x => p.μ.real {x}) e / Real.sqrt (1 + e)) ≤
        ∑' e : ↥(E ∩ Set.Ioi 0),
        ENNReal.ofReal (zetaWeight (fun x => p.μ.real {x}) e / Real.sqrt (1 + e)) := by
      rw [tsum_subtype (E' ∩ Set.Ioi 0)
          (fun e => ENNReal.ofReal (zetaWeight (fun x => p.μ.real {x}) e / Real.sqrt (1 + e))),
        tsum_subtype (E ∩ Set.Ioi 0)
          (fun e => ENNReal.ofReal (zetaWeight (fun x => p.μ.real {x}) e / Real.sqrt (1 + e)))]
      refine ENNReal.tsum_le_tsum fun e => ?_
      by_cases he : e ∈ E ∩ Set.Ioi 0
      · rw [Set.indicator_of_mem he,
          Set.indicator_of_mem (show e ∈ E' ∩ Set.Ioi 0 from ⟨Or.inl he.1, he.2⟩)]
      · by_cases he' : e ∈ E' ∩ Set.Ioi 0
        · -- `e ∉ E`, so `e ∉ Z_ζ ∪ E` and `μ({e}) = 0`
          rw [Set.indicator_of_mem he']
          have heE : e ∉ E := fun h => he ⟨h, he'.2⟩
          have heZ : e ∉ Zzeta := fun hz => Set.disjoint_left.mp hE'Z he'.1 hz
          have h0 : p.μ {e} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr
            (show e ∈ (Zzeta ∪ E)ᶜ from fun h => h.elim heZ heE)) hμ
          simp [zetaWeight, measureReal_def, h0]
        · rw [Set.indicator_of_notMem he']
          exact zero_le
    exact ne_top_of_le_ne_top hsum hle
  exact extra_zeros_countable_admissible hE'c hE'Z hsymm hp hμ' hν (Or.inl hsum')

/-- **Theorem B(b) for finite `E`, from the countable form** (the statement of `theoremB'`, Theorem 3.8 for
finite `E`): obtained from the ledger axiom `brs_countable_meanvalue`, without the Landau step. -/
theorem theoremB_finite_of_countable {E : Set ℝ} (hE : E.Finite) (hEZ : Disjoint E Zzeta) {p : Pair}
    (hp : p ∈ K) (hμ : CarriedBy p.μ (Zzeta ∪ E)) (hν : CarriedBy p.ν BRSNodes) :
    RiemannHypothesis ∧ p = pZeta :=
  theoremB_b_countable hE.countable hEZ hp hμ hν (weightedCond_of_finite hE _)

end PosRig
