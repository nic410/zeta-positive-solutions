/-
# The headline results of Paper I (§1.3): Theorems A, B, C, D and the Corollary

Each theorem below is stated as in §1.3 of the paper, with the definitions of `Basic.lean`, and proved
from Mathlib and the ledger axioms of `Ledger.lean`.  `axioms.log` records `#print axioms` for each.

The headline theorems of v1.0 are kept unchanged (`theoremA`, `logic_display`, `conjS_equivalences`,
`theoremB'`, `corollary_magic`, `theoremC`, `theoremD'`); in v1.1 `theoremB'` is the finite case of
Theorem B(b), `corollary_magic` the finite case of the second sentence of the Corollary, and `theoremD'` the
strict-(Mg) case of Theorem D.  The v1.1 headline results are `theoremB_a`, `theoremB_b`,
`corollary_magic_a` and `theoremD_nonstrict'` (end of this file).  In v1.2 the statement of `theoremC` (a)
changes with the paper: its certified numbers are those of the exact member `F₁₁₁` (`ExactMember.lean`), and it
states `κ* ≤ κ*_OPS` and the classical conductor bound `e^{−2πκ*_OPS} ≥ 1 − 8.98 · 10^{-1060}` as well.
-/
import PositivityRigidity.Criticality
import PositivityRigidity.Uniqueness
import PositivityRigidity.Criterion
import PositivityRigidity.Certified
import PositivityRigidity.CountableExtras
import PositivityRigidity.CriterionWeak
import PositivityRigidity.NearRigidity

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

set_option exponentiation.threshold 2000

/-- **Theorem A (duality and criticality).**
(a) `𝒦 ≠ ∅` iff `𝒜(F) ≥ 0` for every `F ∈ 𝒞`, iff `κ* ≥ 0`; and `q_min = e^{−2πκ*}`: `κ*` is finite,
and `e^{−2πκ*}` is the least conductor `q > 0` for which `𝒜_q` has an admissible pair (for `q > 0`,
`𝒦(𝒜_q) ≠ ∅ ⇔ q ≥ e^{−2πκ*}`).
(b) Assume (E).  Then `κ* = 0` iff every admissible `μ` is purely atomic, iff all admissible `μ` are
carried by one discrete set (`DiscreteSet`: closed and discrete, i.e. without accumulation point in `ℝ`).
(Theorem 2.7(a), Proposition 2.10, Theorem 2.12(b).) -/
theorem theoremA :
    ((K.Nonempty ↔ ∀ F ∈ Cone, 0 ≤ Arch F) ∧ ((∀ F ∈ Cone, 0 ≤ Arch F) ↔ 0 ≤ kappaStar) ∧
      kappaStar ≠ ⊥ ∧ kappaStar ≠ ⊤ ∧
      (∀ q : ℝ, 0 < q →
        ((Kset (Arch_q q) xi2).Nonempty ↔ Real.exp (-2 * Real.pi * kappaStar.toReal) ≤ q)) ∧
      IsLeast {q : ℝ | 0 < q ∧ (Kset (Arch_q q) xi2).Nonempty}
        (Real.exp (-2 * Real.pi * kappaStar.toReal))) ∧
    (CondE →
      (kappaStar = 0 ↔ ∀ p ∈ K, PurelyAtomic p.μ) ∧
      (kappaStar = 0 ↔ ∃ Z : Set ℝ, DiscreteSet Z ∧ ∀ p ∈ K, CarriedBy p.μ Z)) := by
  refine ⟨⟨duality_i_ii, duality_ii_iv, kappaStar_ne_bot, kappaStar_ne_top,
    fun q hq => conductor_form hq, ⟨⟨Real.exp_pos _, (conductor_form (Real.exp_pos _)).mpr le_rfl⟩,
      fun q hq => (conductor_form hq.1).mp hq.2⟩⟩, fun hE => ?_⟩
  obtain ⟨h1, h2, -⟩ := criticality hE
  exact ⟨h1, h2⟩

/-- **The logic of (E), (U), (S) and RH** (§1.2, Theorem 2.9):
`RH ⇒ (E)`, `(U) ⇒ (S)`, and `(U) ⇔ [(E) ⇒ RH] ∧ [RH ⇒ 𝒦 = {p_ζ}]`. -/
theorem logic_display :
    (RiemannHypothesis → CondE) ∧ (CondU → CondS) ∧
    (CondU ↔ (CondE → RiemannHypothesis) ∧ (RiemannHypothesis → K = {pZeta})) :=
  ⟨fun h => (logic_a h).2, logic_d.1, logic_c.1⟩

/-- **Conjecture S, the stated equivalences** (§1.2, Proposition 2.10, Lemma 2.5, Proposition 2.8):
`κ* ≤ 0` ⇔ `q_min ≥ 1` ⇔ no admissible pair has a zero measure `μ ≥ λ dt` with `λ > 0`. -/
theorem conjS_equivalences :
    (CondS ↔ 1 ≤ qmin) ∧ (CondS ↔ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam → ¬ DominatesLeb p.μ lam) := by
  refine ⟨condS_iff_qmin, ⟨fun hS p hp lam hlam hdom => ?_, fun h => ?_⟩⟩
  · have := slack_ge_of_dominates homog_Arch (scalable_ConeG_Arch xi2) hp hlam.le hdom
    have h2 : ((lam : ℝ) : EReal) ≤ 0 := this.trans hS
    exact absurd (EReal.coe_nonpos.mp h2) (not_le.mpr hlam)
  · unfold CondS
    by_contra hpos
    push Not at hpos
    obtain ⟨p, hp, hdom⟩ := prop_2_8_dominates.mp hpos.le
    have hk : 0 < kappaStar.toReal := by
      have := kappaStar_coe
      rw [← this] at hpos
      exact_mod_cast hpos
    exact h p hp _ hk hdom

/-- **Theorem B(b) for finite `E` (the v1.0 Theorem B).**  Let `E ⊂ ℝ \ Z_ζ` be finite.  If `(μ, ν) ∈ 𝒦`,
`μ` is carried by `Z_ζ ∪ E`, and `ν` is carried by `ℳ = {log m/(4π) : m ≥ 1}`, then RH holds and
`(μ, ν) = p_ζ`.  (Theorem 3.8 for finite `E`, applied to `E ∪ (−E)`; this proof uses the Landau step,
ledger axiom `brs_lemma36_landau`.  The same statement is derived from the countable form, without the
Landau step, as `theoremB_finite_of_countable`.) -/
theorem theoremB' {E : Set ℝ} (hE : E.Finite) (hEZ : Disjoint E Zzeta) {p : Pair} (hp : p ∈ K)
    (hμ : CarriedBy p.μ (Zzeta ∪ E)) (hν : CarriedBy p.ν BRSNodes) :
    RiemannHypothesis ∧ p = pZeta :=
  theoremB hE hEZ hp hμ hν

/-- **Corollary (magic-function principle), second sentence, finite case.**  If some `F ∈ 𝒞` with
`𝒜(F) = 0` has only finitely many real zeros outside `Z_ζ`, and the zeros of `F̂` in `[ξ₂, ∞)` lie in `ℳ`,
then (U) holds; if moreover (E) holds, then RH holds and `𝒦 = {p_ζ}`.  (Corollary 3.9(b) for finite `E`.) -/
theorem corollary_magic {F : ℂ → ℂ} (hF : F ∈ Cone) (hA : Arch F = 0)
    (hfin : (ZF F \ Zzeta).Finite) (hZhat : ZhatF F ⊆ BRSNodes) :
    CondU ∧ (CondE → RiemannHypothesis ∧ K = {pZeta}) :=
  magic_function_principle hF hA hfin hZhat

/-- **Remark 4.10(b), first sentence.**  If `κ* = 0` and some weak magic function `F*` has only finitely
many real zeros outside `Z_ζ` and `Ẑ(F*) ⊆ ℳ`, then RH holds and `𝒦 = {p_ζ}`: `κ* = 0` gives (E)
(Theorem 2.7), every admissible pair is carried by `Z(F*) × Ẑ(F*)` (Theorem 2.12(c)), and Theorem 3.8
applies.  (The last sentences of the remark, `Z(F*) ⊆ Z_ζ ∪ {0}`, are `remark_4_10b_zero`.) -/
theorem remark_4_10b (h0 : kappaStar = 0) {Fs : ℝ → ℝ} (hFs : IsWeakMagic Fs)
    (hfin : ({t : ℝ | Fs t = 0} \ Zzeta).Finite)
    (hZhat : {ξ : ℝ | xi2 ≤ ξ ∧ 𝓕 (fun t : ℝ => (Fs t : ℂ)) ξ = 0} ⊆ BRSNodes) :
    RiemannHypothesis ∧ K = {pZeta} := by
  have hE : CondE := condE_iff_kappaStar_nonneg.mpr h0.symm.le
  have hall : ∀ p ∈ K, RiemannHypothesis ∧ p = pZeta := by
    intro p hp
    have hμ := weakMagic_carries_mu hFs hp
    have hν := (weakMagic_carries_nu hFs hp).1
    refine theoremB hfin Set.disjoint_sdiff_left hp ?_
      (measure_mono_null (Set.compl_subset_compl.mpr hZhat) hν)
    exact measure_mono_null (Set.compl_subset_compl.mpr (by
      intro t ht
      by_cases h : t ∈ Zzeta
      · exact Or.inl h
      · exact Or.inr ⟨ht, h⟩)) hμ
  obtain ⟨p, hp⟩ := hE
  obtain ⟨hRH, rfl⟩ := hall p hp
  exact ⟨hRH, Set.Subset.antisymm (fun q hq => (hall q hq).2) (Set.singleton_subset_iff.mpr hp)⟩

/-- **Theorem C (near-criticality).**
(a) `κ* ≤ κ*_OPS ≤ 1.4291572 · 10^{-1060}`.  Hence `q_min ≥ 1 − 8.98 · 10^{-1060}`, and the same bound holds
already in the classical Odlyzko–Poitou–Serre cone: `e^{−2πκ*_OPS} ≥ 1 − 8.98 · 10^{-1060}`.
(b) `κ* ≥ −2.7112 · 10^{-3}`.
(Theorem 5.1, Corollary 5.2, Proposition 5.10; (a) through the exact member `F₁₁₁ ∈ 𝒞_OPS` of Proposition 4.5,
certified without a cushion, Proposition 5.7.) -/
theorem theoremC :
    (kappaStar ≤ kappaOPS ∧ kappaOPS ≤ (((14291572 : ℝ) / 10 ^ 1067 : ℝ) : EReal) ∧
      1 - (898 : ℝ) / 10 ^ 1062 ≤ qmin ∧ 1 - (898 : ℝ) / 10 ^ 1062 ≤ qminOPS) ∧
    ((-(27112 : ℝ) / 10 ^ 7 : ℝ) : EReal) ≤ kappaStar := by
  have h : ((kappa111 : ℚ) : ℝ) = (14291572 : ℝ) / 10 ^ 1067 := by
    unfold kappa111; push_cast; ring
  refine ⟨⟨kappaStar_le_kappaOPS, ?_, cor_5_2.2.2.2.2.1, cor_5_2.2.2.2.2.2⟩, prop_5_8_kappa⟩
  rw [← h]
  exact kappaOPS_le_kappa111

/-- **Theorem D with the strict (Mg) of v1.0.**  If the exact Hermite family `F_J = Ξ² P_J(t²)` satisfies
(N), (G_a), (Z_∞) and the strict (Mg) of v1.0 (`HypMg`), then (S) and (U) hold, and `RH ⇔ (E)`; under
either, `κ* = 0` and `𝒦 = {p_ζ}`.  (Theorem 4.8 of v1.0; the v1.1 Theorem D, with the non-strict (Mg), is
`theoremD_nonstrict'`, and `hypMg0_of_hypMg` shows that it implies this one.) -/
theorem theoremD' (hN : HypN) (hG : HypG) (hZ : HypZinf) (hMg : HypMg) :
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
      (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) :=
  (theoremD hN hG hZ hMg).2

/-! ## v1.1 headline results -/

/-- **Theorem B(a) (v1.1).**  Let `(μ, ν) ∈ 𝒦`.  If `μ` is carried by `Z_ζ ∪ {0}`, then RH holds and
`(μ, ν) = p_ζ`.  No condition on `ν` is needed.  (Theorem 3.6.) -/
theorem theoremB_a {p : Pair} (hp : p ∈ K) (hμ : CarriedBy p.μ (Zzeta ∪ {0})) :
    RiemannHypothesis ∧ p = pZeta :=
  zero_support_theorem hp hμ

/-- **Theorem B(b) (v1.1).**  Let `(μ, ν) ∈ 𝒦` and let `E ⊂ ℝ \ Z_ζ` be countable.  If `μ` is carried by
`Z_ζ ∪ E`, `ν` is carried by `ℳ`, and `Σ_{e ∈ E, e > 0} μ({e}) |ζ(1/2 + ie)| (1 + e)^{-1/2} < ∞`, then RH
holds and `(μ, ν) = p_ζ`.  (Theorem 3.8 applied to `E ∪ (−E)`; for finite `E` the condition holds,
`weightedCond_of_finite`.) -/
theorem theoremB_b {E : Set ℝ} (hEc : E.Countable) (hEZ : Disjoint E Zzeta) {p : Pair} (hp : p ∈ K)
    (hμ : CarriedBy p.μ (Zzeta ∪ E)) (hν : CarriedBy p.ν BRSNodes)
    (hsum : WeightedCond E (fun x => p.μ.real {x})) : RiemannHypothesis ∧ p = pZeta :=
  theoremB_b_countable hEc hEZ hp hμ hν hsum

/-- **Corollary (magic-function principle), first sentence (v1.1).**  If some `F ∈ 𝒞` with `𝒜(F) = 0` has
every real zero in `Z_ζ ∪ {0}`, then (U) holds; if moreover (E) holds, then RH holds and `𝒦 = {p_ζ}`.
(Corollary 3.9(a).) -/
theorem corollary_magic_a {F : ℂ → ℂ} (hF : F ∈ Cone) (hA : Arch F = 0) (hZ : ZF F ⊆ Zzeta ∪ {0}) :
    CondU ∧ (CondE → RiemannHypothesis ∧ K = {pZeta}) :=
  magic_principle_zero hF hA hZ

/-- **Theorem D (v1.1; a criterion through the zero-killing family).**  If the exact Hermite family
`F_J = Ξ² P_J(t²)` satisfies the hypotheses (N), (G_a), (Z_∞) and (Mg) of Theorem 4.8, (Mg) being
`liminf_{J ∈ 𝒥} F̂_J(ξ) ≥ 0` for every `ξ ≥ ξ₂`, then (S) and (U) hold, and `RH ⇔ (E)`; under either,
`κ* = 0` and `𝒦 = {p_ζ}`.  (Theorem 4.8.) -/
theorem theoremD_nonstrict' (hN : HypN) (hG : HypG) (hZ : HypZinf) (hMg : HypMg0) :
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧
      (RiemannHypothesis ∨ CondE → kappaStar = 0 ∧ K = {pZeta}) :=
  (theoremD_nonstrict hN hG hZ hMg).2

end PosRig
