/-
§3.2: the values (3.3) of `𝒜` on a BRS basis, and Proposition 3.5 (uniqueness on `ζ`'s support) in
the signed form used in the proof of Theorem 3.8, for **every** basis `B` with the defining properties
`IsBRSBasis B` of Definition 3.4, proved from the ledger axioms `explicit_formula` (Lemma 2.3) and
`riemannZeta_neg_of_mem_Ioo` (no zeros of `ζ` in `(0, 1)`), with the reflection symmetries of the zeros
from Mathlib and Zeta23.
-/
import PositivityRigidity.Sanity
import PositivityRigidity.Zeta
import PositivityRigidity.BRSDefs
import PositivityRigidity.Faithful

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRig

/-! ## Facts about the non-trivial zeros -/

theorem NontrivialZeros.ne_one {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 1 := by
  rintro rfl
  simp [NontrivialZeros] at hρ

theorem NontrivialZeros.one_le_mult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ mult ρ :=
  PosRig.one_le_mult hρ.1 (NontrivialZeros.ne_one hρ)

theorem conj_mem_NontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    (starRingEnd ℂ) ρ ∈ NontrivialZeros := by
  obtain ⟨hz, h0, h1⟩ := hρ
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  rw [riemannZeta_conj, hz, map_zero]

/-- The zeros are symmetric under `ρ ↦ 1 − ρ` (functional equation, via Zeta23's `zeta_reflect_zero`
for `ρ ↦ 1 − ρ̄` and conjugation). -/
theorem one_sub_mem_NontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    1 - ρ ∈ NontrivialZeros := by
  have h := Zeta23.zeta_reflect_zero ((starRingEnd ℂ) ρ) (conj_mem_NontrivialZeros hρ)
  have e : Zeta23.reflect ((starRingEnd ℂ) ρ) = 1 - ρ := by
    simp [Zeta23.reflect]
  rw [e] at h
  exact h

theorem mult_one_sub {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : mult (1 - ρ) = mult ρ := by
  unfold mult analyticOrderNatAt
  rw [Zeta23.analyticOrderAt_zeta_one_sub hρ.2.1 hρ.2.2]

theorem mult_conj {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : mult ((starRingEnd ℂ) ρ) = mult ρ := by
  unfold mult analyticOrderNatAt
  rw [Zeta23.analyticOrderAt_zeta_conj (NontrivialZeros.ne_one hρ)]

/-- There are no real zeros in the critical strip (`ζ(σ) < 0` on `(0, 1)`). -/
theorem NontrivialZeros.im_ne_zero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.im ≠ 0 := by
  intro him
  obtain ⟨hz, h0, h1⟩ := hρ
  have hρr : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hneg := riemannZeta_neg_of_mem_Ioo ρ.re h0 h1
  rw [← hρr, hz] at hneg
  exact lt_irrefl _ hneg

theorem tOf_one_sub (ρ : ℂ) : tOf (1 - ρ) = -tOf ρ := by
  unfold tOf; ring

/-! ## The explicit formula on complex BRS-type functions -/

private theorem rePart_add_imPart' (F : ℂ → ℂ) (z : ℂ) : rePart F z + I * imPart F z = F z := by
  unfold rePart imPart
  field_simp
  ring

/-- Lemma 2.3 extended by complex linearity to a function whose real and imaginary parts lie in `𝒯`. -/
theorem ArchC_EF {F : ℂ → ℂ} (hre : rePart F ∈ TestClass) (him : imPart F ∈ TestClass) :
    ArchC F = (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * F (tOf ρ)) +
      (1 / Real.pi : ℂ) *
        ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n) := by
  obtain ⟨hs1, hp1, h1⟩ := explicit_formula _ hre
  obtain ⟨hs2, hp2, h2⟩ := explicit_formula _ him
  have hFT : ∀ ξ, FT F ξ = FT (rePart F) ξ + I * FT (imPart F) ξ := by
    intro ξ
    have hsplit : F = fun z => rePart F z + I * imPart F z := by
      funext z; rw [rePart_add_imPart']
    conv_lhs => rw [hsplit]
    rw [FT_add_of_integrable (G := fun z => I * imPart F z) (TestClass.integrable hre)
      ((TestClass.integrable him).const_mul I), FT_smul]
  have hz : (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * F (tOf ρ)) =
      (∑' ρ : NontrivialZeros, (mult ρ : ℂ) * rePart F (tOf ρ)) +
        I * ∑' ρ : NontrivialZeros, (mult ρ : ℂ) * imPart F (tOf ρ) := by
    rw [← tsum_mul_left, ← hs1.tsum_add (hs2.mul_left I)]
    congr 1
    funext ρ
    rw [← rePart_add_imPart' F (tOf ρ)]
    ring
  have hp : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT F (xiOf n)) =
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          FT (rePart F) (xiOf n)) +
        I * ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          FT (imPart F) (xiOf n) := by
    rw [← tsum_mul_left, ← hp1.tsum_add (hp2.mul_left I)]
    congr 1
    funext n
    rw [hFT]
    ring
  unfold ArchC
  rw [h1, h2, hz, hp]
  ring

/-! ## The values (3.3) -/

/-- `ξ_n = log(n²)/(4π)`: the prime-power nodes are BRS nodes. -/
theorem xiOf_eq_brsNode_sq (n : ℕ) : xiOf n = brsNode (n ^ 2) := by
  unfold xiOf brsNode
  push_cast
  rw [Real.log_pow]
  field_simp
  ring

theorem vonMangoldt_coef_zero :
    ((ArithmeticFunction.vonMangoldt 0 / Real.sqrt 0 : ℝ) : ℂ) = 0 := by
  simp

/-! ## Pairings with atoms on `Z_ζ` and on `ℳ` -/

theorem pairAtoms_eq_zero {w : ℝ → ℝ} {F : ℂ → ℂ} (h : ∀ x : ℝ, w x ≠ 0 → F x = 0) :
    pairAtoms w F = 0 := by
  unfold pairAtoms
  refine (tsum_congr fun x => ?_).trans tsum_zero
  by_cases hx : w x = 0
  · simp [hx]
  · simp [h x hx]

/-! ## Statements about a basis with the BRS properties

Everything below holds for **every** `B : BRSBasis` with `IsBRSBasis B` (Definition 3.4); no
identification of `B` with a particular basis is used. -/

section BRSBasisSection

variable {B : BRSBasis} (hB : IsBRSBasis B)
include hB

/-! ## The defining properties of a BRS basis `B` -/

theorem brsU_props {m : ℕ} (hm : 1 ≤ m) :
    Differentiable ℂ (B.U m) ∧ (∀ z, B.U m (-z) = B.U m z) ∧
      rePart (B.U m) ∈ TestClass ∧ imPart (B.U m) ∈ TestClass :=
  hB.2.1 m hm

theorem brsV_props (v : VIndex) :
    Differentiable ℂ (B.V v) ∧ (∀ z, B.V v (-z) = B.V v z) ∧
      rePart (B.V v) ∈ TestClass ∧ imPart (B.V v) ∈ TestClass :=
  hB.2.2.1 v

theorem brsU_interp {m : ℕ} (hm : 1 ≤ m) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) {j : ℕ}
    (hj : j < mult ρ) : iteratedDeriv j (B.U m) (tOf ρ) = 0 :=
  hB.2.2.2.1 m hm ρ hρ j hj

theorem brsU_FT {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    FT (B.U m) (brsNode m') = if m = m' then 1 else 0 :=
  hB.2.2.2.2.1 m m' hm hm'

theorem brsV_interp (v : VIndex) {ρ' : ℂ} (hρ' : ρ' ∈ NontrivialZeros) (him : 0 < ρ'.im) {j' : ℕ}
    (hj' : j' < mult ρ') : iteratedDeriv j' (B.V v) (tOf ρ') = if v.val = (ρ', j') then 1 else 0 :=
  hB.2.2.2.2.2.1 v ρ' hρ' him j' hj'

theorem brsV_FT (v : VIndex) {m : ℕ} (hm : 1 ≤ m) : FT (B.V v) (brsNode m) = 0 :=
  hB.2.2.2.2.2.2 v m hm

/-- The prime side of `𝒜(U_m)`: `Σ_n Λ(n) n^{-1/2} Û_m(ξ_n) = Λ(√m) m^{-1/4}`. -/
theorem primeSum_brsU {m : ℕ} (hm : 1 ≤ m) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (B.U m) (xiOf n) =
      ((nuZetaAtom m : ℝ) : ℂ) := by
  have hterm : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      FT (B.U m) (xiOf n) =
      if n ^ 2 = m then ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) else 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [xiOf_eq_brsNode_sq, brsU_FT hB hm (Nat.one_le_pow _ _ hn)]
      by_cases h : n ^ 2 = m
      · rw [if_pos h.symm, if_pos h, mul_one]
      · rw [if_neg (fun h' => h h'.symm), if_neg h, mul_zero]
  simp_rw [hterm]
  unfold nuZetaAtom
  by_cases hsq : IsSquare m
  · obtain ⟨r, hr⟩ := hsq
    have hr2 : r ^ 2 = m := by rw [hr]; ring
    rw [tsum_eq_single r (fun n hn => by
      rw [if_neg]
      intro h
      exact hn (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (h.trans hr2.symm)))]
    rw [if_pos hr2, if_pos ⟨r, hr⟩]
    have hsqrt : Nat.sqrt m = r := by rw [← hr2]; exact Nat.sqrt_eq' r
    rw [hsqrt]
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at hr; omega
      · exact h
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hm' : (m : ℝ) = (r : ℝ) ^ 2 := by rw [← hr2]; push_cast; ring
    congr 1
    rw [hm', div_eq_mul_inv]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le, ← Real.rpow_neg hr0.le]
    norm_num
  · rw [if_neg hsq]
    push_cast
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [if_neg]
    rintro rfl
    exact hsq ⟨n, by ring⟩

theorem primeSum_brsV (v : VIndex) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * FT (B.V v) (xiOf n) =
      0 := by
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [xiOf_eq_brsNode_sq, brsV_FT hB v (Nat.one_le_pow _ _ hn), mul_zero]

theorem brsU_at_zero {m : ℕ} (hm : 1 ≤ m) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    B.U m (tOf ρ) = 0 := by
  have h := brsU_interp hB hm hρ (j := 0) (NontrivialZeros.one_le_mult hρ)
  simpa using h

theorem zeroSum_brsU {m : ℕ} (hm : 1 ≤ m) :
    ∑' ρ : NontrivialZeros, (mult ρ : ℂ) * B.U m (tOf ρ) = 0 := by
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  rw [brsU_at_zero hB hm ρ.2, mul_zero]

/-- **(3.3), first value.** `𝒜(U_m) = π^{-1} Λ(√m) m^{-1/4}`. -/
theorem ArchC_brsU {m : ℕ} (hm : 1 ≤ m) :
    ArchC (B.U m) = ((nuZetaAtom m / Real.pi : ℝ) : ℂ) := by
  obtain ⟨-, -, hre, him⟩ := brsU_props hB hm
  rw [ArchC_EF hre him, zeroSum_brsU hB hm, primeSum_brsU hB hm]
  push_cast
  ring

/-- `V_v` at a non-trivial zero `ρ'` with `Im ρ' > 0`. -/
theorem brsV_at_upper (v : VIndex) {ρ' : ℂ} (hρ' : ρ' ∈ NontrivialZeros) (him : 0 < ρ'.im) :
    B.V v (tOf ρ') = if v.val = (ρ', 0) then 1 else 0 := by
  have h := brsV_interp hB v hρ' him (j' := 0) (NontrivialZeros.one_le_mult hρ')
  simpa using h

/-- `V_v` at a non-trivial zero `ρ'` with `Im ρ' < 0`: by evenness, the value at `1 − ρ'`. -/
theorem brsV_at_lower (v : VIndex) {ρ' : ℂ} (hρ' : ρ' ∈ NontrivialZeros) (him : ρ'.im < 0) :
    B.V v (tOf ρ') = if v.val = (1 - ρ', 0) then 1 else 0 := by
  have h1 := one_sub_mem_NontrivialZeros hρ'
  have him' : 0 < (1 - ρ').im := by simp; linarith
  rw [← brsV_at_upper hB v h1 him', tOf_one_sub, (brsV_props hB v).2.1]

/-- The zero side of `𝒜(V_{ρ,0})`: `Σ_{ρ'} m(ρ') V_{ρ,0}(t_{ρ'}) = 2 m(ρ)` (the zeros with `Im ρ' < 0` are
the `1 − ρ''` with `Im ρ'' > 0`; there are no zeros with `Im ρ' = 0`). -/
theorem zeroSum_brsV0 (v : VIndex) (hv : v.val.2 = 0) :
    ∑' ρ' : NontrivialZeros, (mult ρ' : ℂ) * B.V v (tOf ρ') = 2 * (mult v.val.1 : ℂ) := by
  set ρ := v.val.1 with hρdef
  have hρ : ρ ∈ NontrivialZeros := v.2.1
  have him : 0 < ρ.im := v.2.2.1
  have hvval : v.val = (ρ, 0) := Prod.ext rfl hv
  have h1 := one_sub_mem_NontrivialZeros hρ
  have him1 : (1 - ρ).im < 0 := by simp; linarith
  have hne : (⟨ρ, hρ⟩ : NontrivialZeros) ≠ ⟨1 - ρ, h1⟩ := by
    intro h
    have := congrArg (fun x : NontrivialZeros => (x : ℂ).im) h
    simp only [Complex.sub_im, Complex.one_im, zero_sub] at this
    linarith
  rw [tsum_eq_sum (s := {⟨ρ, hρ⟩, ⟨1 - ρ, h1⟩})]
  · rw [Finset.sum_pair hne]
    simp only
    rw [brsV_at_upper hB v hρ him, brsV_at_lower hB v h1 him1, sub_sub_cancel, if_pos hvval,
      mult_one_sub hρ]
    ring
  · intro ρ' hρ'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ'
    obtain ⟨hne1, hne2⟩ := hρ'
    rcases lt_trichotomy (ρ' : ℂ).im 0 with hlt | heq | hgt
    · rw [brsV_at_lower hB v ρ'.2 hlt, if_neg, mul_zero]
      intro h
      rw [hvval] at h
      apply hne2
      apply Subtype.ext
      have h' := (Prod.ext_iff.mp h).1
      simp only at h' ⊢
      rw [h']
      ring
    · exact absurd heq (NontrivialZeros.im_ne_zero ρ'.2)
    · rw [brsV_at_upper hB v ρ'.2 hgt, if_neg, mul_zero]
      intro h
      rw [hvval] at h
      apply hne1
      apply Subtype.ext
      exact ((Prod.ext_iff.mp h).1).symm

/-- **(3.3), second value.** `𝒜(V_{ρ,0}) = 2 m(ρ)`. -/
theorem ArchC_brsV0 (v : VIndex) (hv : v.val.2 = 0) : ArchC (B.V v) = 2 * (mult v.val.1 : ℂ) := by
  obtain ⟨-, -, hre, him⟩ := brsV_props hB v
  rw [ArchC_EF hre him, zeroSum_brsV0 hB v hv, primeSum_brsV hB v, mul_zero, add_zero]

theorem pairNodes_brsV (ν : ℕ → ℝ) (v : VIndex) : pairNodes ν (FT (B.V v)) = 0 := by
  unfold pairNodes
  refine (tsum_congr fun m => ?_).trans tsum_zero
  split_ifs with hm
  · rw [brsV_FT hB v hm, mul_zero]
  · rfl

theorem pairNodes_brsU (ν : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    pairNodes ν (FT (B.U m)) = (ν m : ℂ) := by
  unfold pairNodes
  rw [tsum_eq_single m]
  · rw [if_pos hm, brsU_FT hB hm hm, if_pos rfl, mul_one]
  · intro m' hm'
    split_ifs with h1
    · rw [brsU_FT hB hm h1, if_neg (Ne.symm hm'), mul_zero]
    · rfl

/-- `V_v` at a positive real zero ordinate `x ∈ Z_ζ`. -/
theorem brsV_at_Zzeta (v : VIndex) {x : ℝ} (hx : x ∈ Zzeta) (hpos : 0 < x) :
    B.V v (x : ℂ) = if v.val = (1 / 2 + I * (x : ℂ), 0) then 1 else 0 := by
  have h := brsV_at_upper hB v (half_add_mem_NontrivialZeros hx) (by simpa using hpos)
  rwa [tOf_half_add] at h

/-- `V_v` at any real zero ordinate `x ∈ Z_ζ` (evenness for `x < 0`; `0 ∉ Z_ζ`). -/
theorem brsV_at_Zzeta' (v : VIndex) {x : ℝ} (hx : x ∈ Zzeta) :
    B.V v (x : ℂ) = if v.val = (1 / 2 + I * ((|x| : ℝ) : ℂ), 0) then 1 else 0 := by
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · have hx' : -x ∈ Zzeta := neg_mem_Zzeta.mpr hx
    have e : B.V v (x : ℂ) = B.V v ((-x : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, (brsV_props hB v).2.1]
    rw [e, brsV_at_Zzeta hB v hx' (by linarith), abs_of_neg hneg]
  · subst h0; exact absurd hx zero_not_mem_Zzeta
  · rw [brsV_at_Zzeta hB v hx hpos, abs_of_pos hpos]

/-! ## Proposition 3.5 (signed form) -/

/-- Step 1 of Proposition 3.5: an off-line zero `ρ₀` with `Im ρ₀ > 0` is impossible, since testing
on `V_{ρ₀,0}` gives `ℛ_{μ,ν}(V_{ρ₀,0}) = 0` (it vanishes on `Z_ζ` and its transform on `ℳ`) while
`𝒜(V_{ρ₀,0}) = 2 m(ρ₀) ≠ 0`. -/
theorem re_eq_half_of_BRSIdentity {w : ℝ → ℝ} {ν : ℕ → ℝ}
    (hsupp : ∀ x, w x ≠ 0 → x ∈ Zzeta) (hid : BRSIdentity B w ν) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) (him : 0 < ρ.im) : ρ.re = 1 / 2 := by
  by_contra hre
  let v : VIndex := ⟨(ρ, 0), hρ, him, NontrivialZeros.one_le_mult hρ⟩
  have hV := hid.2 v
  rw [ArchC_brsV0 hB v rfl, pairNodes_brsV hB, mul_zero, add_zero] at hV
  have hA : pairAtoms w (B.V v) = 0 := by
    apply pairAtoms_eq_zero
    intro x hx
    rw [brsV_at_Zzeta' hB v (hsupp x hx), if_neg]
    intro h
    apply hre
    have h' : ρ = 1 / 2 + I * ((|x| : ℝ) : ℂ) := (Prod.ext_iff.mp h).1
    rw [h']
    simp
  rw [hA] at hV
  have h1 := NontrivialZeros.one_le_mult hρ
  have h2 : (mult ρ : ℂ) = 0 := by
    have : (2 : ℂ) * (mult ρ : ℂ) = 0 := hV
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have h3 : mult ρ = 0 := by exact_mod_cast h2
  omega

/-- **Proposition 3.5, in the signed form used in the proof of Theorem 3.8** (the statement of the
former ledger axiom `support_uniqueness`).  Let `μ = Σ w(x)δ_x` be an even real measure carried by
`Z_ζ` and `ν = Σ ν_m δ_{log m/4π}` a real measure carried by `ℳ` such that
`𝒜(F) = ∫ F dμ + (1/π)∫ F̂ dν` for every BRS function `F`.  Then RH holds, `μ = μ_ζ`
(`w(γ) = m_γ` on `Z_ζ`) and `ν = ν_ζ` (`ν_m = Λ(√m) m^{-1/4}`). -/
theorem support_uniqueness_thm : ∀ (w : ℝ → ℝ) (ν : ℕ → ℝ),
    (∀ x, w (-x) = w x) → (∀ x, w x ≠ 0 → x ∈ Zzeta) → BRSIdentity B w ν →
    RiemannHypothesis ∧ (∀ γ ∈ Zzeta, w γ = mult (1 / 2 + I * (γ : ℂ))) ∧
      ∀ m : ℕ, 1 ≤ m → ν m = nuZetaAtom m := by
  intro w ν heven hsupp hid
  refine ⟨?_, ?_, ?_⟩
  · -- RH: every non-trivial zero is on the critical line
    apply RH_iff_critical.mpr
    intro ρ hρ
    rcases lt_trichotomy ρ.im 0 with hlt | heq | hgt
    · have hc := conj_mem_NontrivialZeros hρ
      have := re_eq_half_of_BRSIdentity hB hsupp hid hc (by simpa using hlt)
      simpa using this
    · exact absurd heq (NontrivialZeros.im_ne_zero hρ)
    · exact re_eq_half_of_BRSIdentity hB hsupp hid hρ hgt
  · -- the zero measure: test on `V_{1/2+iγ,0}`
    have hpos : ∀ γ ∈ Zzeta, 0 < γ → w γ = mult (1 / 2 + I * (γ : ℂ)) := by
      intro γ hγ hγpos
      have hρ := half_add_mem_NontrivialZeros hγ
      have him : 0 < (1 / 2 + I * (γ : ℂ)).im := by simpa using hγpos
      let v : VIndex := ⟨(1 / 2 + I * (γ : ℂ), 0), hρ, him, NontrivialZeros.one_le_mult hρ⟩
      have hV := hid.2 v
      rw [ArchC_brsV0 hB v rfl, pairNodes_brsV hB, mul_zero, add_zero] at hV
      have hne : γ ≠ -γ := by intro h; linarith
      have hA : pairAtoms w (B.V v) = (w γ : ℂ) + (w (-γ) : ℂ) := by
        unfold pairAtoms
        rw [tsum_eq_sum (s := {γ, -γ})]
        · rw [Finset.sum_pair hne, brsV_at_Zzeta hB v hγ hγpos, if_pos rfl,
            brsV_at_Zzeta' hB v (neg_mem_Zzeta.mpr hγ), abs_neg, abs_of_pos hγpos, if_pos rfl]
          ring
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
          by_cases hw : w x = 0
          · simp [hw]
          · rw [brsV_at_Zzeta' hB v (hsupp x hw), if_neg, mul_zero]
            intro h
            have h' : (1 / 2 + I * (γ : ℂ)) = 1 / 2 + I * ((|x| : ℝ) : ℂ) := (Prod.ext_iff.mp h).1
            have h'' : γ = |x| := by
              have := congrArg Complex.im h'
              simpa using this
            rcases abs_choice x with hax | hax
            · exact hx.1 (by rw [h'', hax])
            · exact hx.2 (by rw [h'', hax]; ring)
      rw [hA, heven γ] at hV
      have hV' : (2 : ℂ) * (mult (1 / 2 + I * (γ : ℂ)) : ℂ) = (w γ : ℂ) + (w γ : ℂ) := hV
      have : (2 : ℂ) * (w γ : ℂ) = 2 * (mult (1 / 2 + I * (γ : ℂ)) : ℂ) := by
        rw [hV']; ring
      have h2 : (w γ : ℂ) = (mult (1 / 2 + I * (γ : ℂ)) : ℂ) :=
        mul_left_cancel₀ two_ne_zero this
      exact_mod_cast h2
    intro γ hγ
    rcases lt_trichotomy γ 0 with hneg | h0 | hgt
    · have hγ' : -γ ∈ Zzeta := neg_mem_Zzeta.mpr hγ
      have := hpos (-γ) hγ' (by linarith)
      rw [heven γ] at this
      rw [this, mult_neg γ]
    · subst h0; exact absurd hγ zero_not_mem_Zzeta
    · exact hpos γ hγ hgt
  · -- the prime measure: test on `U_m`
    intro m hm
    have hU := hid.1 m hm
    have hA : pairAtoms w (B.U m) = 0 := by
      apply pairAtoms_eq_zero
      intro x hx
      have hxZ := hsupp x hx
      have h := brsU_at_zero hB hm (half_add_mem_NontrivialZeros hxZ)
      rwa [tOf_half_add] at h
    rw [ArchC_brsU hB hm, hA, pairNodes_brsU hB ν hm, zero_add] at hU
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : ((nuZetaAtom m : ℝ) : ℂ) = (ν m : ℂ) := by
      have : ((nuZetaAtom m / Real.pi : ℝ) : ℂ) = (1 / Real.pi : ℂ) * (ν m : ℂ) := hU
      push_cast at this
      field_simp at this
      linear_combination this
    exact_mod_cast h2.symm

end BRSBasisSection

end PosRig
