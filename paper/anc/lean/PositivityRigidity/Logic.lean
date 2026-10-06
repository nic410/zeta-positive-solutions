/-
§2.3: Theorem 2.9 (the logic of (E), (U) and RH), and the last clause of Proposition 2.10.
-/
import PositivityRigidity.Duality
import PositivityRigidity.PZeta

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-- **Theorem 2.9(a).** RH implies `p_ζ ∈ 𝒦`; hence RH implies (E). -/
theorem logic_a (hRH : RiemannHypothesis) : pZeta ∈ K ∧ CondE :=
  ⟨pZeta_mem_K_of_RH hRH, ⟨pZeta, pZeta_mem_K_of_RH hRH⟩⟩

/-- **Theorem 2.9(b).** If `(μ, ν_ζ) ∈ 𝒦` for some `μ`, then RH holds and `μ = μ_ζ`
(ledger axiom `logic_b`). -/
theorem logic_b' {μ : Measure ℝ} (h : (⟨μ, nuZeta⟩ : Pair) ∈ K) : RiemannHypothesis ∧ μ = muZeta :=
  logic_b μ h

/-- **Theorem 2.9(c).** (U) holds iff both `(E) ⇒ RH` and `RH ⇒ 𝒦 = {p_ζ}` hold.  In particular
`(E) ∧ (U) ⇒ RH`, and (U) implies `RH ⇔ (E) ⇔ κ* ≥ 0`. -/
theorem logic_c :
    (CondU ↔ (CondE → RiemannHypothesis) ∧ (RiemannHypothesis → K = {pZeta})) ∧
    (CondE ∧ CondU → RiemannHypothesis) ∧
    (CondU → (RiemannHypothesis ↔ CondE) ∧ (CondE ↔ 0 ≤ kappaStar)) := by
  have key : CondU ↔ (CondE → RiemannHypothesis) ∧ (RiemannHypothesis → K = {pZeta}) := by
    constructor
    · intro hU
      refine ⟨?_, ?_⟩
      · rintro ⟨p, hp⟩
        have hpz : p = pZeta := hU hp
        subst hpz
        exact (logic_b' hp).1
      · intro hRH
        exact Set.Subset.antisymm hU (Set.singleton_subset_iff.mpr (logic_a hRH).1)
    · rintro ⟨h1, h2⟩ p hp
      have hRH := h1 ⟨p, hp⟩
      have := h2 hRH
      rw [this] at hp
      exact hp
  refine ⟨key, ?_, ?_⟩
  · rintro ⟨hE, hU⟩
    exact (key.mp hU).1 hE
  · intro hU
    refine ⟨⟨fun hRH => (logic_a hRH).2, (key.mp hU).1⟩, condE_iff_kappaStar_nonneg⟩

/-- **Theorem 2.9(d).** (U) ⇒ (S).  Consequently `(U) ∧ (E) ⇒ κ* = 0`, and `(U) ∧ ¬RH ⇒ 𝒦 = ∅` and
`κ* < 0`. -/
theorem logic_d :
    (CondU → CondS) ∧ (CondU ∧ CondE → kappaStar = 0) ∧
    (CondU ∧ ¬ RiemannHypothesis → K = ∅ ∧ kappaStar < 0) := by
  have hUS : CondU → CondS := by
    intro hU
    unfold CondS
    by_contra hpos
    push Not at hpos
    obtain ⟨p, hp, hdom⟩ := prop_2_8_dominates.mp hpos.le
    have hpz : p = pZeta := hU hp
    subst hpz
    have hk : 0 < kappaStar.toReal := by
      have := kappaStar_coe
      rw [← this] at hpos
      exact_mod_cast hpos
    exact not_dominatesLeb_muZeta hk hdom
  refine ⟨hUS, ?_, ?_⟩
  · rintro ⟨hU, hE⟩
    exact le_antisymm (hUS hU) (condE_iff_kappaStar_nonneg.mp hE)
  · rintro ⟨hU, hnRH⟩
    have hnE : ¬ CondE := fun hE => hnRH ((logic_c.1.mp hU).1 hE)
    refine ⟨Set.not_nonempty_iff_eq_empty.mp hnE, ?_⟩
    by_contra h
    push Not at h
    exact hnE (condE_iff_kappaStar_nonneg.mpr h)

/-- **Proposition 2.10, last clause.** RH ⇒ `q_min ≤ 1`. -/
theorem qmin_le_one_of_RH (hRH : RiemannHypothesis) : qmin ≤ 1 := by
  have h0 : 0 ≤ kappaStar := condE_iff_kappaStar_nonneg.mp (logic_a hRH).2
  unfold qmin
  rw [Real.exp_le_one_iff]
  have : 0 ≤ kappaStar.toReal := EReal.toReal_nonneg h0
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- `p_ζ` is admissible if and only if RH holds (§2.1, Theorem 2.9(a), (b)). -/
theorem pZeta_mem_K_iff_RH : pZeta ∈ K ↔ RiemannHypothesis :=
  ⟨fun h => (logic_b' h).1, fun h => (logic_a h).1⟩

end PosRig
