/-
Measures carried by countable sets (Mathlib only): integrals are sums over atoms, and such measures
are determined by their atoms.  Used to pass between admissible pairs (measures) and the atom-weight
form of Theorem 3.8.  Also: numerical bounds for `log 3`, `log 5` (Proposition 5.11).
-/
import PositivityRigidity.Basic

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped ENNReal

namespace PosRig

/-- A measure carried by `S` is its own restriction to `S`. -/
theorem restrict_eq_self_of_carriedBy {μ : Measure ℝ} {S : Set ℝ} (hμ : CarriedBy μ S) :
    μ.restrict S = μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  exact hμ

theorem integral_eq_tsum_of_carriedBy {μ : Measure ℝ} {S : Set ℝ} (hS : S.Countable)
    (hμ : CarriedBy μ S) {f : ℝ → ℂ} (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' x : ℝ, ((μ.real {x} : ℝ) : ℂ) * f x := by
  have hrestr := restrict_eq_self_of_carriedBy hμ
  have h1 : ∫ x, f x ∂μ = ∫ x in S, f x ∂μ := by rw [hrestr]
  rw [h1, setIntegral_countable f hS hf.integrableOn]
  have hsupp : Function.support (fun x : ℝ => ((μ.real {x} : ℝ) : ℂ) * f x) ⊆ S := by
    intro x hx
    by_contra hxS
    apply hx
    have hx0 : μ {x} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr hxS) hμ
    simp [measureReal_def, hx0]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  congr 1

theorem brsNode_injOn : Set.InjOn brsNode {m : ℕ | 1 ≤ m} := by
  intro m hm m' hm' h
  simp only [Set.mem_ofPred_eq] at hm hm'
  simp only [brsNode] at h
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  have hlog : Real.log (m : ℝ) = Real.log (m' : ℝ) := by
    field_simp at h
    exact h
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0' : (0 : ℝ) < m' := by exact_mod_cast hm'
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr hm0) (Set.mem_Ioi.mpr hm0') hlog
  exact_mod_cast this

theorem BRSNodes_countable : BRSNodes.Countable := by
  apply (Set.countable_range brsNode).mono
  rintro x ⟨m, -, rfl⟩
  exact ⟨m, rfl⟩

theorem integral_eq_tsum_brsNodes {ν : Measure ℝ} (hν : CarriedBy ν BRSNodes) {f : ℝ → ℂ}
    (hf : Integrable f ν) :
    ∫ x, f x ∂ν = ∑' m : ℕ, if 1 ≤ m then ((ν.real {brsNode m} : ℝ) : ℂ) * f (brsNode m) else 0 := by
  rw [integral_eq_tsum_of_carriedBy BRSNodes_countable hν hf]
  set G : ℝ → ℂ := fun x => ((ν.real {x} : ℝ) : ℂ) * f x with hG
  -- support of `G` is in `BRSNodes`
  have hsuppG : Function.support G ⊆ BRSNodes := by
    intro x hx
    by_contra hxS
    apply hx
    have hx0 : ν {x} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr hxS) hν
    simp [hG, measureReal_def, hx0]
  -- reindex by `m ↦ brsNode m` on `{m | 1 ≤ m}`
  let g : {m : ℕ // 1 ≤ m} → ℝ := fun m => brsNode m.1
  have hg : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (brsNode_injOn a.2 b.2 hab)
  have hrange : Function.support G ⊆ Set.range g := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hsuppG hx
    exact ⟨⟨m, hm⟩, rfl⟩
  have h1 : ∑' m : {m : ℕ // 1 ≤ m}, G (g m) = ∑' x, G x := hg.tsum_eq hrange
  rw [← h1]
  -- the `ite` sum over ℕ is the sum over `{m | 1 ≤ m}`
  have hsupp2 : Function.support
      (fun m : ℕ => if 1 ≤ m then ((ν.real {brsNode m} : ℝ) : ℂ) * f (brsNode m) else 0) ⊆
      {m : ℕ | 1 ≤ m} := by
    intro m hm
    by_contra h
    apply hm
    simp only [Set.mem_ofPred_eq] at h
    simp [h]
  rw [← tsum_subtype_eq_of_support_subset hsupp2]
  apply tsum_congr
  intro m
  have hm : 1 ≤ (m : ℕ) := m.2
  simp only [hm, if_true, hG, g]

theorem measure_eq_of_carriedBy {μ μ' : Measure ℝ} {S : Set ℝ} (hS : S.Countable)
    (hμ : CarriedBy μ S) (hμ' : CarriedBy μ' S) (h : ∀ x ∈ S, μ {x} = μ' {x}) : μ = μ' := by
  rw [← restrict_eq_self_of_carriedBy hμ, ← restrict_eq_self_of_carriedBy hμ']
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  have hc : (A ∩ S).Countable := hS.mono Set.inter_subset_right
  have hmeas : ∀ y ∈ A ∩ S, MeasurableSet ((id : ℝ → ℝ) ⁻¹' {y}) := by
    intro y _
    exact measurableSet_singleton y
  have e1 := tsum_measure_preimage_singleton (μ := μ) hc hmeas
  have e2 := tsum_measure_preimage_singleton (μ := μ') hc hmeas
  simp only [Set.preimage_id_eq, id_eq] at e1 e2
  rw [← e1, ← e2]
  apply tsum_congr
  intro b
  have hb : (b : ℝ) ∈ S := b.2.2
  simpa using h b hb

theorem EvenMeasure.singleton {μ : Measure ℝ} (h : EvenMeasure μ) (x : ℝ) : μ {-x} = μ {x} := by
  have hmeas : Measurable (fun t : ℝ => -t) := measurable_neg
  calc μ {-x} = (Measure.map (fun t : ℝ => -t) μ) {-x} := by rw [h]
    _ = μ ((fun t : ℝ => -t) ⁻¹' {-x}) := Measure.map_apply hmeas (measurableSet_singleton _)
    _ = μ {x} := by
      congr 1
      ext t
      simp

/-- Partial sums of the series for `log (1 - x)`, used for the numerical bounds below. -/
theorem log_one_sub_bounds {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - |x| ^ (n + 1) / (1 - |x|) ≤ Real.log (1 - x) ∧
    Real.log (1 - x) ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + |x| ^ (n + 1) / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem log_five_bounds :
    (16094379 : ℝ) / 10 ^ 7 < Real.log 5 ∧ Real.log 5 < (16094380 : ℝ) / 10 ^ 7 := by
  have h5 : Real.log 5 = 2 * Real.log 2 + Real.log (1 - (-1 / 4 : ℝ)) := by
    have : (5 : ℝ) = 2 ^ 2 * (1 - (-1 / 4 : ℝ)) := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hx : |(-1 / 4 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  obtain ⟨hlo, hhi⟩ := log_one_sub_bounds hx 15
  have habs : |(-1 / 4 : ℝ)| = 1 / 4 := by rw [abs_of_neg (by norm_num)]; norm_num
  rw [habs] at hlo hhi
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlo hhi
  norm_num at hlo hhi
  have l2lo := Real.log_two_gt_d9
  have l2hi := Real.log_two_lt_d9
  rw [h5]
  constructor
  · norm_num at l2lo ⊢
    linarith
  · norm_num at l2hi ⊢
    linarith

theorem log_three_bounds :
    (10986122 : ℝ) / 10 ^ 7 < Real.log 3 ∧ Real.log 3 < (10986123 : ℝ) / 10 ^ 7 := by
  have h3 : Real.log 3 = 2 * Real.log 2 + Real.log (1 - (1 / 4 : ℝ)) := by
    have : (3 : ℝ) = 2 ^ 2 * (1 - (1 / 4 : ℝ)) := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hx : |(1 / 4 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  obtain ⟨hlo, hhi⟩ := log_one_sub_bounds hx 15
  have habs : |(1 / 4 : ℝ)| = 1 / 4 := by rw [abs_of_pos (by norm_num)]
  rw [habs] at hlo hhi
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlo hhi
  norm_num at hlo hhi
  have l2lo := Real.log_two_gt_d9
  have l2hi := Real.log_two_lt_d9
  rw [h3]
  constructor
  · norm_num at l2lo ⊢
    linarith
  · norm_num at l2hi ⊢
    linarith

end PosRig
