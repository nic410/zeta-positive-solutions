/-
Lemma A.2 (positive-coefficient certificates), Appendix A.1 of the paper (Mathlib only).

These are the elementary positivity criteria by coefficient signs that the certificates of
Theorem 5.1 (node neighbourhoods, Taylor models) and Propositions 5.4 and 5.5 (positivity of the
Gaussian–Laguerre polynomials, window lower bounds after a Möbius map) apply to explicit polynomials.
They are proved here outright; the certificates themselves remain ledger axioms.
-/
import Mathlib

namespace PosRig

open Polynomial

/-- `p(x) = q(x − c)` for `q = p(c + t) = p.comp (X + C c)`. -/
theorem eval_comp_X_add_C_sub (p : Polynomial ℝ) (c x : ℝ) :
    (p.comp (Polynomial.X + Polynomial.C c)).eval (x - c) = p.eval x := by
  rw [Polynomial.eval_comp]
  simp

/-- **Lemma A.2(a) (Descartes at `c`), first claim** (Appendix A.1; used by the certificates of
Theorem 5.1 and Propositions 5.4, 5.5).  If every coefficient of `p(c + t)` is non-negative and the
constant term is positive, then `p > 0` on `[c, ∞)`. -/
theorem posc_a (p : Polynomial ℝ) (c : ℝ)
    (h : ∀ i, 0 ≤ (p.comp (Polynomial.X + Polynomial.C c)).coeff i)
    (h0 : 0 < (p.comp (Polynomial.X + Polynomial.C c)).coeff 0) :
    ∀ x, c ≤ x → 0 < p.eval x := by
  intro x hx
  rw [← eval_comp_X_add_C_sub p c x, Polynomial.eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (h i) (pow_nonneg (sub_nonneg.mpr hx) i)
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simpa using h0⟩

/-- **Lemma A.2(a) (Descartes at `c`), second claim** (Appendix A.1; used by the certificates of
Theorem 5.1 and Propositions 5.4, 5.5).  If `p` vanishes to exact order `m` at `c` (the coefficients of
`t^i`, `i < m`, of `p(c + t)` vanish and `p ≠ 0`) and the coefficients of `t^m, t^{m+1}, …` (up to the
degree) in `p(c + t)` are positive, then `p > 0` on `(c, ∞)`. -/
theorem posc_a' (p : Polynomial ℝ) (c : ℝ) (m : ℕ)
    (hlow : ∀ i < m, (p.comp (X + C c)).coeff i = 0)
    (hpos : ∀ i, m ≤ i → i ≤ (p.comp (X + C c)).natDegree → 0 < (p.comp (X + C c)).coeff i)
    (hne : p.comp (X + C c) ≠ 0) :
    ∀ x, c < x → 0 < p.eval x := by
  intro x hx
  set q := p.comp (X + C c) with hq
  have ht : 0 < x - c := sub_pos.mpr hx
  have hm : m ≤ q.natDegree := by
    by_contra hlt
    have h1 : q.coeff q.natDegree = 0 := hlow q.natDegree (not_le.mp hlt)
    exact hne (Polynomial.leadingCoeff_eq_zero.mp h1)
  rw [← eval_comp_X_add_C_sub p c x, ← hq, Polynomial.eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro i hi
    rcases lt_or_ge i m with h1 | h1
    · rw [hlow i h1, zero_mul]
    · exact (mul_pos (hpos i h1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        (pow_pos ht i)).le
  · exact ⟨q.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _),
      mul_pos (hpos _ hm le_rfl) (pow_pos ht _)⟩

/-- **Lemma A.2(b), non-negativity** (Appendix A.1; used by the certificates of Theorem 5.1 and
Propositions 5.4, 5.5).  A polynomial with non-negative coefficients is non-negative on the
non-negative orthant. -/
theorem posc_b {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (h : ∀ s, 0 ≤ p.coeff s)
    (v : σ → ℝ) (hv : ∀ i, 0 ≤ v i) : 0 ≤ MvPolynomial.eval v p := by
  rw [MvPolynomial.eval_eq]
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (h s) (Finset.prod_nonneg fun i _ => pow_nonneg (hv i) _)

/-- **Lemma A.2(b), positivity** (Appendix A.1; used by the certificates of Theorem 5.1 and
Propositions 5.4, 5.5).  A polynomial with non-negative coefficients is positive at every point `v` of
the non-negative orthant at which some monomial with a positive coefficient is positive. -/
theorem posc_b' {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (h : ∀ s, 0 ≤ p.coeff s)
    (v : σ → ℝ) (hv : ∀ i, 0 ≤ v i) (s₀ : σ →₀ ℕ) (hs₀ : 0 < p.coeff s₀)
    (hmono : 0 < (s₀.prod fun i k => v i ^ k)) : 0 < MvPolynomial.eval v p := by
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (h s) (Finset.prod_nonneg fun i _ => pow_nonneg (hv i) _)
  · exact ⟨s₀, MvPolynomial.mem_support_iff.mpr hs₀.ne', mul_pos hs₀ hmono⟩

end PosRig
