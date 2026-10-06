/-
§3.3–3.4: Theorem 3.8 for finite `E` (v1.0 Theorem 3.7), Theorem B(b) for finite `E` (v1.0 Theorem B),
and Corollary 3.9(b) for finite `E` (v1.0 Corollary 3.8, the magic-function principle).  The countable
forms of v1.1 are in `CountableExtras.lean`, Theorem 3.6 and Corollary 3.9(a) in `ZeroSupport.lean`.

Theorem 3.8 for finite `E` is proved for every basis `B` with the properties of Definition 3.4 and every
coefficient function `α` for which Lemma 3.7 (3.4) and the Landau step (v1.0 Lemma B.3) hold, from
Proposition 3.5 in its signed form
(`support_uniqueness_thm`, proved in `BRSValues.lean` from the ledger axioms `explicit_formula` and
`riemannZeta_neg_of_mem_Ioo`) and `Ξ(0) > 0`; the proof is the paper's: positivity enters only through
the residue class `2 mod 3`.  The admissible-pair form (and Theorem B) obtains such `(B, α)` from the
ledger axiom `brs_lemma36_landau`.
-/
import PositivityRigidity.Logic
import PositivityRigidity.Atoms
import PositivityRigidity.BRSDefs
import PositivityRigidity.BRSValues

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

/-! ## Arithmetic of the class `2 mod 3` -/

/-- If `N ≡ 2 (mod 3)` and `k² ∣ N`, then `N/k² ≡ 2 (mod 3)` (proof of Theorem 3.8). -/
theorem mod3_div_sq {N k : ℕ} (hN : N % 3 = 2) (hk : k ^ 2 ∣ N) : (N / k ^ 2) % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hN
  have hk2 : 0 < k ^ 2 := by positivity
  rw [Nat.mul_div_cancel_left m hk2]
  have h1 := Nat.mod_lt k (show 3 > 0 by norm_num)
  have h2 := Nat.mod_lt m (show 3 > 0 by norm_num)
  rw [Nat.mul_mod, Nat.pow_mod] at hN
  interval_cases hk' : k % 3 <;> interval_cases hm' : m % 3 <;> simp_all

/-- No `N ≡ 2 (mod 3)` is a square. -/
theorem not_isSquare_of_mod3 {N : ℕ} (hN : N % 3 = 2) : ¬ IsSquare N := by
  rintro ⟨r, rfl⟩
  have h1 := Nat.mod_lt r (show 3 > 0 by norm_num)
  rw [Nat.mul_mod] at hN
  interval_cases hr : r % 3 <;> simp_all

theorem sqInd_of_mod3 {N : ℕ} (hN : N % 3 = 2) : sqInd N = 0 := by
  unfold sqInd
  rw [if_neg (not_isSquare_of_mod3 hN)]

/-- `C_N ≥ 0` for `N ≡ 2 (mod 3)` as soon as `ν ≥ 0` on the class `2 mod 3`. -/
theorem CN_nonneg_of_mod3 {ν : ℕ → ℝ} (hpos : ∀ m : ℕ, m % 3 = 2 → 0 ≤ ν m) {N : ℕ}
    (hN : N % 3 = 2) : 0 ≤ CN ν N := by
  unfold CN
  refine Finset.sum_nonneg fun k hk => ?_
  have hk' := (Finset.mem_filter.mp hk).2.2
  unfold ell
  exact mul_nonneg (by positivity) (hpos _ (mod3_div_sq hN hk'))

/-! ## Theorem 3.8 in atom-weight form -/

/-- **Theorem 3.8 for finite `E` (v1.0 Theorem 3.7, finitely many extra zeros).**  Let `B` be a basis
with the properties of Definition 3.4 and `α` a coefficient function for which Lemma 3.7 (3.4) and the
Landau step (v1.0 Lemma B.3) hold (for instance
the BRS basis and the coefficients of (3.1)).  Let `E ⊂ ℝ \ Z_ζ` be finite and symmetric.  Let
`μ = Σ w(x)δ_x` be an even real measure carried by `Z_ζ ∪ E` and `ν = Σ ν_m δ_{log m/4π}` a real measure
carried by `ℳ` such that `𝒜(F) = ∫ F dμ + (1/π)∫ F̂ dν` for every function `F` of the basis.  Assume
`ν({log m/4π}) ≥ 0` for every `m ≡ 2 (mod 3)`, and `μ({0}) ≥ 0` if `0 ∈ E`.  Then RH holds, `μ = μ_ζ`
and `ν = ν_ζ`. -/
theorem thm_3_7 {B : BRSBasis} {α : ℕ → ℂ → ℂ} (hB : IsBRSBasis B) (h36 : Lemma36 B α)
    (hB3 : LemmaB3 α) (E : Finset ℝ) (hEZ : ∀ e ∈ E, e ∉ Zzeta) (hsymm : ∀ e ∈ E, -e ∈ E)
    (w : ℝ → ℝ) (ν : ℕ → ℝ) (heven : ∀ x, w (-x) = w x)
    (hsupp : ∀ x, w x ≠ 0 → x ∈ Zzeta ∨ x ∈ E) (hid : BRSIdentity B w ν)
    (hpos : ∀ m : ℕ, m % 3 = 2 → 0 ≤ ν m) (h0 : (0 : ℝ) ∈ E → 0 ≤ w 0) :
    RiemannHypothesis ∧ (∀ x, x ∉ Zzeta → w x = 0) ∧
      (∀ γ ∈ Zzeta, w γ = mult (1 / 2 + I * (γ : ℂ))) ∧ ∀ m : ℕ, 1 ≤ m → ν m = nuZetaAtom m := by
  have h34 := h36 E hEZ hsymm w ν heven hsupp hid
  -- positivity on the class `2 mod 3` gives `c_N(E) ≥ 0` there
  have hc : ∀ N : ℕ, N % 3 = 2 → 0 ≤ cN α E w N := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have h := h34 N hN1
    rw [sqInd_of_mod3 hN, mul_zero, Complex.ofReal_zero, add_zero] at h
    rw [← h]
    exact Complex.zero_le_real.mpr (CN_nonneg_of_mod3 hpos hN)
  -- `ϱ̃_0 ≥ 0`, since `μ({0}) ≥ 0` and `Ξ(0) > 0`
  have hrho0 : (0 : ℝ) ∈ E.filter (fun e => 0 ≤ e) → 0 ≤ rhoTilde w 0 := by
    intro hmem
    have hw0 := h0 (Finset.mem_filter.mp hmem).1
    unfold rhoTilde
    rw [if_pos rfl]
    have := Xi_zero_pos
    positivity
  -- the Landau step
  have hzero := hB3 (E.filter (fun e => 0 ≤ e)) (fun e he => (Finset.mem_filter.mp he).2)
    (rhoTilde w) hrho0 hc
  -- hence no extra atoms
  have hwE : ∀ e ∈ E, w e = 0 := by
    have hpos' : ∀ e ∈ E, 0 ≤ e → w e = 0 := by
      intro e he hge
      have hr := hzero e (Finset.mem_filter.mpr ⟨he, hge⟩)
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
  obtain ⟨hRH, hw, hν⟩ := support_uniqueness_thm hB w ν heven hsupp' hid
  refine ⟨hRH, fun x hx => ?_, hw, hν⟩
  by_contra hne
  exact hx (hsupp' x hne)

/-! ## From admissible pairs to atom weights -/

theorem rePart_add_imPart (F : ℂ → ℂ) (z : ℂ) : rePart F z + I * imPart F z = F z := by
  unfold rePart imPart
  field_simp
  ring

/-- The identity of Definition 2.4 extended by complex linearity to a function whose real and
imaginary parts lie in `𝒯` (Definition 2.1, last sentence). -/
theorem admissible_identityC {p : Pair} (hp : p ∈ K) {F : ℂ → ℂ}
    (hre : rePart F ∈ TestClass) (him : imPart F ∈ TestClass) :
    Integrable (onR F) p.μ ∧ Integrable (FT F) p.ν ∧
      ArchC F = (∫ t, F t ∂p.μ) + (1 / Real.pi : ℂ) * ∫ ξ, FT F ξ ∂p.ν := by
  obtain ⟨-, -, hid⟩ := hp
  obtain ⟨hr1, hr2, hr3⟩ := hid _ hre
  obtain ⟨hi1, hi2, hi3⟩ := hid _ him
  have hsplit : F = fun z => rePart F z + I * imPart F z := by
    funext z; rw [rePart_add_imPart]
  have hFT : FT F = fun ξ => FT (rePart F) ξ + I * FT (imPart F) ξ := by
    funext ξ
    conv_lhs => rw [hsplit]
    rw [FT_add_of_integrable (G := fun z => I * imPart F z) (TestClass.integrable hre)
      ((TestClass.integrable him).const_mul I), FT_smul]
  have honR : onR F = fun t => onR (rePart F) t + I * onR (imPart F) t := by
    funext t; simp only [onR]; rw [rePart_add_imPart]
  refine ⟨?_, ?_, ?_⟩
  · rw [honR]; exact hr1.add (hi1.const_mul I)
  · rw [hFT]; exact hr2.add (hi2.const_mul I)
  · have e1 : ∫ t, F t ∂p.μ = (∫ t, rePart F t ∂p.μ) + I * ∫ t, imPart F t ∂p.μ := by
      have : (fun t : ℝ => F t) = fun t => onR (rePart F) t + I * onR (imPart F) t := honR
      rw [this, integral_add hr1 (hi1.const_mul I), integral_const_mul]
      rfl
    have e2 : ∫ ξ, FT F ξ ∂p.ν = (∫ ξ, FT (rePart F) ξ ∂p.ν) + I * ∫ ξ, FT (imPart F) ξ ∂p.ν := by
      rw [hFT, integral_add hr2 (hi2.const_mul I), integral_const_mul]
    unfold ArchC
    rw [hr3, hi3, e1, e2]
    ring

/-- **Theorem 3.8 for finite `E`, last sentences (and its form with the identity on `𝒯`).**  Let
`E ⊂ ℝ \ Z_ζ` be finite and symmetric.  Every admissible pair carried by `(Z_ζ ∪ E) × ℳ` is `p_ζ`, and RH holds. -/
theorem thm_3_7_admissible {E : Set ℝ} (hE : E.Finite) (hEZ : Disjoint E Zzeta)
    (hsymm : ∀ e ∈ E, -e ∈ E) {p : Pair} (hp : p ∈ K) (hμ : CarriedBy p.μ (Zzeta ∪ E))
    (hν : CarriedBy p.ν BRSNodes) : RiemannHypothesis ∧ p = pZeta := by
  obtain ⟨hlfμ, hlfν⟩ := Admissible.isLocallyFinite hp
  have hfinμ : ∀ x : ℝ, p.μ {x} ≠ ⊤ := fun x => (isCompact_singleton.measure_lt_top).ne
  have hfinν : ∀ x : ℝ, p.ν {x} ≠ ⊤ := fun x => (isCompact_singleton.measure_lt_top).ne
  have hScount : (Zzeta ∪ E).Countable := Zzeta_countable.union hE.countable
  set w : ℝ → ℝ := fun x => p.μ.real {x} with hw
  set ν' : ℕ → ℝ := fun m => p.ν.real {brsNode m} with hν'
  obtain ⟨B, α, hB, h36, hB3⟩ := brs_lemma36_landau
  obtain ⟨-, hU, hV, -, -, -, -⟩ := id hB
  -- the identity on the BRS functions, in atom-weight form
  have hpair : ∀ F : ℂ → ℂ, rePart F ∈ TestClass → imPart F ∈ TestClass →
      ArchC F = pairAtoms w F + (1 / Real.pi : ℂ) * pairNodes ν' (FT F) := by
    intro F hre him
    obtain ⟨h1, h2, h3⟩ := admissible_identityC hp hre him
    have e1 := integral_eq_tsum_of_carriedBy hScount hμ h1
    have e2 := integral_eq_tsum_brsNodes hν h2
    simp only [onR] at e1
    rw [h3, e1, e2]
    rfl
  have hid : BRSIdentity B w ν' :=
    ⟨fun m hm => hpair _ (hU m hm).2.2.1 (hU m hm).2.2.2,
      fun v => hpair _ (hV v).2.2.1 (hV v).2.2.2⟩
  have heven : ∀ x, w (-x) = w x := by
    intro x
    simp only [hw, measureReal_def, EvenMeasure.singleton hp.1 x]
  have hsupp : ∀ x, w x ≠ 0 → x ∈ Zzeta ∨ x ∈ hE.toFinset := by
    intro x hx
    by_contra hnot
    apply hx
    have hx' : x ∉ Zzeta ∪ E := by
      simp only [Set.mem_union, Set.Finite.mem_toFinset] at hnot ⊢; exact hnot
    have : p.μ {x} = 0 := measure_mono_null (Set.singleton_subset_iff.mpr hx') hμ
    simp [hw, measureReal_def, this]
  obtain ⟨hRH, hwoff, hwZ, hνZ⟩ := thm_3_7 hB h36 hB3 hE.toFinset
    (fun e he => Set.disjoint_left.mp hEZ ((Set.Finite.mem_toFinset hE).mp he))
    (fun e he => (Set.Finite.mem_toFinset hE).mpr (hsymm e ((Set.Finite.mem_toFinset hE).mp he)))
    w ν' heven hsupp hid (fun m _ => measureReal_nonneg)
    (fun _ => measureReal_nonneg)
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

/-! ## Theorem B(b) and Corollary 3.9(b), finite `E` -/

/-- **Theorem B(b) for finite `E` (v1.0 Theorem B, uniqueness near `ζ`'s support).**  Let
`E ⊂ ℝ \ Z_ζ` be finite.  If `(μ, ν) ∈ 𝒦`,
`μ` is carried by `Z_ζ ∪ E` and `ν` is carried by `ℳ`, then RH holds and `(μ, ν) = p_ζ`. -/
theorem theoremB {E : Set ℝ} (hE : E.Finite) (hEZ : Disjoint E Zzeta) {p : Pair} (hp : p ∈ K)
    (hμ : CarriedBy p.μ (Zzeta ∪ E)) (hν : CarriedBy p.ν BRSNodes) :
    RiemannHypothesis ∧ p = pZeta := by
  have hE' : (E ∪ (fun x => -x) '' E).Finite := hE.union (hE.image _)
  have hEZ' : Disjoint (E ∪ (fun x => -x) '' E) Zzeta := by
    rw [Set.disjoint_union_left]
    refine ⟨hEZ, Set.disjoint_left.mpr ?_⟩
    rintro x ⟨e, he, rfl⟩ hx
    exact Set.disjoint_left.mp hEZ he (neg_mem_Zzeta.mp hx)
  have hsymm : ∀ e ∈ E ∪ (fun x => -x) '' E, -e ∈ E ∪ (fun x => -x) '' E := by
    rintro e (he | ⟨e', he', rfl⟩)
    · exact Or.inr ⟨e, he, rfl⟩
    · left; simpa using he'
  refine thm_3_7_admissible hE' hEZ' hsymm hp ?_ hν
  exact measure_mono_null (Set.compl_subset_compl.mpr
    (Set.union_subset_union_right _ Set.subset_union_left)) hμ

/-- **Proposition 3.5 (uniqueness on `ζ`'s support).**  Let `(μ, ν) ∈ 𝒦` with `μ` carried by `Z_ζ` and
`ν` carried by `ℳ`.  Then RH holds and `(μ, ν) = p_ζ`.  (Theorem B(b) with `E = ∅`; the signed form used
in its proof is `support_uniqueness_thm`.  For admissible pairs the hypothesis on `ν` can be dropped,
`prop_3_5_strong`.) -/
theorem prop_3_5 {p : Pair} (hp : p ∈ K) (hμ : CarriedBy p.μ Zzeta) (hν : CarriedBy p.ν BRSNodes) :
    RiemannHypothesis ∧ p = pZeta :=
  theoremB Set.finite_empty (Set.empty_disjoint _) hp (by rwa [Set.union_empty]) hν

/-- **Corollary 3.9(b) for finite `E` (v1.0 Corollary 3.8, magic-function principle).**  Suppose some
`F ∈ 𝒞` satisfies `𝒜(F) = 0`, has only
finitely many real zeros outside `Z_ζ`, and has `Ẑ(F) ⊆ ℳ`.  Then (U) holds.  If (E) holds as well, then
RH holds and `𝒦 = {p_ζ}`. -/
theorem magic_function_principle {F : ℂ → ℂ} (hF : F ∈ Cone) (hA : Arch F = 0)
    (hfin : (ZF F \ Zzeta).Finite) (hZhat : ZhatF F ⊆ BRSNodes) :
    CondU ∧ (CondE → RiemannHypothesis ∧ K = {pZeta}) := by
  have hU : CondU := by
    intro p hp
    obtain ⟨hμ, hν⟩ := comp_slackness hF hA hp
    have hμ' : CarriedBy p.μ (Zzeta ∪ (ZF F \ Zzeta)) :=
      measure_mono_null (Set.compl_subset_compl.mpr (by
        intro t ht
        by_cases h : t ∈ Zzeta
        · exact Or.inl h
        · exact Or.inr ⟨ht, h⟩)) hμ
    have hν' : CarriedBy p.ν BRSNodes := measure_mono_null (Set.compl_subset_compl.mpr hZhat) hν
    exact (theoremB hfin Set.disjoint_sdiff_left hp hμ' hν').2
  refine ⟨hU, fun hE => ?_⟩
  obtain ⟨p, hp⟩ := hE
  have hpz : p = pZeta := hU hp
  subst hpz
  -- RH from Theorem B applied to `p_ζ` itself (no Theorem 2.9(b) needed)
  obtain ⟨hμ, hν⟩ := comp_slackness hF hA hp
  have hμ' : CarriedBy pZeta.μ (Zzeta ∪ (ZF F \ Zzeta)) :=
    measure_mono_null (Set.compl_subset_compl.mpr (by
      intro t ht
      by_cases h : t ∈ Zzeta
      · exact Or.inl h
      · exact Or.inr ⟨ht, h⟩)) hμ
  have hRH := (theoremB hfin Set.disjoint_sdiff_left hp hμ'
    (measure_mono_null (Set.compl_subset_compl.mpr hZhat) hν)).1
  exact ⟨hRH, Set.Subset.antisymm hU (Set.singleton_subset_iff.mpr hp)⟩

end PosRig
