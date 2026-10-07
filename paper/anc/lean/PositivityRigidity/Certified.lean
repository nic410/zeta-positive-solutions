/-
§5: the certified bounds.  Proposition 5.4 (the Gaussian–Laguerre function in the classical cone),
Proposition 5.5, Proposition 5.10 and Proposition 5.11, from the certificate axioms of `Ledger.lean`, weak
duality (Lemma 2.5), the normalisation `F ↦ F/∫F`, Proposition 2.10, and exact arithmetic (bounds for `π`,
`log 3`, `log 5`).  Theorem 5.1, Corollary 5.2 and Proposition 5.7, through the exact members `F_J`, are in
`ExactMember.lean`; Corollary 5.3 is in `NearRigidity.lean`.
-/
import PositivityRigidity.Duality
import PositivityRigidity.Atoms
import PositivityRigidity.PZeta

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder ENNReal

namespace PosRig

set_option exponentiation.threshold 2000

/-! ## Weak duality against a floor -/

/-- If an admissible pair has `μ ≥ c dt` (`c ≥ 0`), then `A(F) ≥ c ∫ F` on the cone (Lemma 2.5). -/
theorem le_of_dominates {A : (ℂ → ℂ) → ℝ} {g : ℝ} {p : Pair} (hp : Admissible A g p) {c : ℝ}
    (hc : 0 ≤ c) (hdom : DominatesLeb p.μ c) {F : ℂ → ℂ} (hF : F ∈ ConeG g) : c * intR F ≤ A F := by
  obtain ⟨hiμ, -⟩ := hp.integrable_re hF.1
  obtain ⟨-, h2⟩ := hp.parts_nonneg hF
  have hmono : ∫ t, (F t).re ∂(ENNReal.ofReal c • (volume : Measure ℝ)) ≤ ∫ t, (F t).re ∂p.μ :=
    integral_mono_measure hdom (Eventually.of_forall fun t => ConeG.re_nonneg hF t) hiμ
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] at hmono
  have hreal := hp.real_identity hF.1
  have : 0 ≤ 1 / Real.pi * ∫ ξ, (FT F ξ).re ∂p.ν := by have := Real.pi_pos; positivity
  have hint : intR F = ∫ t : ℝ, (F t).re := rfl
  rw [hint]
  linarith

/-- The slack of `A` at the gap `g` is at least `c` if some pair admissible for `A` at `g` has
`μ ≥ c dt`. -/
theorem slack_ge_of_dominates {A : (ℂ → ℂ) → ℝ} (hA : Homog A) {g : ℝ}
    (hC : ScalableFor A (ConeG g)) {p : Pair} (hp : Admissible A g p) {c : ℝ} (hc : 0 ≤ c)
    (hdom : DominatesLeb p.μ c) : (c : EReal) ≤ slack A (ConeG g) :=
  (le_slack_iff hA hC c).mpr fun _ hF => le_of_dominates hp hc hdom hF

/-- The natural-gap step of Proposition 5.11: a pair whose prime measure lives on `[g', ∞)` is admissible
at every gap `g ≤ g'`. -/
theorem admissible_mono_gap {A : (ℂ → ℂ) → ℝ} {g g' : ℝ} (hg : g ≤ g') {p : Pair}
    (hp : Admissible A g' p) : Admissible A g p :=
  ⟨hp.1, measure_mono_null (Set.compl_subset_compl.mpr (Set.Ici_subset_Ici.mpr hg)) hp.2.1, hp.2.2⟩

/-! ## Proposition 5.4 (the classical cone): the Gaussian–Laguerre certificate -/

/-- The optimised classical (OPS) conductor bound `e^{−2πκ*_OPS}`. -/
def qminOPS : ℝ := Real.exp (-2 * Real.pi * kappaOPS.toReal)

theorem kappaOPS_ne_bot : kappaOPS ≠ ⊥ :=
  ne_bot_of_le_ne_bot kappaStar_ne_bot kappaStar_le_kappaOPS

/-- **Proposition 5.4, the Gaussian–Laguerre certificate.** `κ* ≤ κ*_OPS ≤ 9.9462 · 10^{-41}`; consequently
the classical OPS conductor bound in degree 1, optimised over `𝒞_OPS`, is at least `1 − 6.25 · 10^{-40}`.
(v1.2: the exact member `F₁₁₁ ∈ 𝒞_OPS` gives `κ*_OPS ≤ 1.4291572 · 10^{-1060}`, `thm_5_1`.) -/
theorem prop_5_3 :
    kappaStar ≤ kappaOPS ∧ kappaOPS ≤ (((99462 : ℝ) / 10 ^ 45 : ℝ) : EReal) ∧
      1 - (625 : ℝ) / 10 ^ 42 ≤ qminOPS := by
  obtain ⟨F, hF, hpos, hA⟩ := cert_kappaOPS
  have hle : kappaOPS ≤ (((99461827001452550725 : ℚ) / 10 ^ 60 : ℚ) : ℝ) := by
    have h := slack_le homog_Arch scalable_ConeOPS_Arch hF hpos
    refine h.trans ?_
    have : Arch F / intR F ≤ (((99461827001452550725 : ℚ) / 10 ^ 60 : ℚ) : ℝ) := by
      rw [div_le_iff₀ hpos]; exact_mod_cast hA
    exact_mod_cast this
  have hnum : (((99461827001452550725 : ℚ) / 10 ^ 60 : ℚ) : ℝ) ≤ (99462 : ℝ) / 10 ^ 45 := by
    push_cast; norm_num
  refine ⟨kappaStar_le_kappaOPS, hle.trans (by exact_mod_cast hnum), ?_⟩
  have hk : kappaOPS.toReal ≤ (99462 : ℝ) / 10 ^ 45 := by
    have := hle.trans (EReal.coe_le_coe_iff.mpr hnum)
    rw [← EReal.coe_toReal kappaOPS_ne_top kappaOPS_ne_bot] at this
    exact_mod_cast this
  unfold qminOPS
  have h2 := Real.add_one_le_exp (-2 * Real.pi * kappaOPS.toReal)
  have hpi := Real.pi_lt_d20
  have hpi0 := Real.pi_pos
  have : 2 * Real.pi * kappaOPS.toReal ≤ (625 : ℝ) / 10 ^ 42 := by
    rcases le_or_gt 0 kappaOPS.toReal with h | h
    · have : 2 * Real.pi * kappaOPS.toReal ≤ 2 * 3.14159265358979323847 * ((99462 : ℝ) / 10 ^ 45) := by
        gcongr
      have h' : 2 * 3.14159265358979323847 * ((99462 : ℝ) / 10 ^ 45) ≤ (625 : ℝ) / 10 ^ 42 := by
        norm_num
      linarith
    · nlinarith
  linarith

/-! ## Proposition 5.5 (low-height rigidity of every admissible pair) -/

theorem TestClass.even_real {F : ℂ → ℂ} (hF : F ∈ TestClass) (t : ℝ) : F (-(t : ℂ)) = F t := by
  obtain ⟨δ, h⟩ := hF
  exact h.even (t : ℂ) (by simp [closedStrip]; linarith [h.pos])

/-- Weak duality on a zero-side window `I ⊂ (0, ∞)`: `μ(I) ≤ 𝒜(F)/(2 min_I F)` (`μ` even). -/
theorem zero_window_bound {F : ℂ → ℂ} (hF : F ∈ Cone) {p : Pair} (hp : p ∈ K) {lo hi m : ℝ}
    (hlo : 0 < lo) (hm : 0 < m) (hb : ∀ t : ℝ, lo ≤ t → t ≤ hi → m ≤ (F t).re) :
    p.μ (Set.Icc lo hi) ≤ ENNReal.ofReal (Arch F / (2 * m)) := by
  set I := Set.Icc lo hi
  set I' := (fun t : ℝ => -t) ⁻¹' I
  have hI : MeasurableSet I := measurableSet_Icc
  have hI' : MeasurableSet I' := measurable_neg hI
  have hdisj : Disjoint I I' := by
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 := ht.1
    have h2 : lo ≤ -t := ht'.1
    linarith
  have hb' : ∀ t ∈ I ∪ I', m ≤ (F t).re := by
    rintro t (ht | ht)
    · exact hb t ht.1 ht.2
    · have := hb (-t) ht.1 ht.2
      rwa [Complex.ofReal_neg, TestClass.even_real hF.1] at this
  have hw := weak_duality hp hF (hI.union hI') MeasurableSet.empty hm.le le_rfl hb' (by simp)
  simp only [measure_empty, mul_zero, add_zero] at hw
  have heven : p.μ I' = p.μ I := by
    have h := hp.1
    unfold EvenMeasure at h
    rw [← Measure.map_apply measurable_neg hI, h]
  rw [measure_union hdisj hI', heven, ← two_mul, ← mul_assoc] at hw
  have h2m : ENNReal.ofReal m * 2 = ENNReal.ofReal (2 * m) := by
    rw [ENNReal.ofReal_mul (by norm_num), mul_comm, ENNReal.ofReal_ofNat]
  rw [h2m] at hw
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.le_div_iff_mul_le
    (Or.inl (by simp [hm])) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hw

/-- Weak duality on a prime-side set `J`: `ν(J) ≤ π 𝒜(F)/min_J F̂`. -/
theorem prime_window_bound {F : ℂ → ℂ} (hF : F ∈ Cone) {p : Pair} (hp : p ∈ K) {J : Set ℝ}
    (hJ : MeasurableSet J) {m : ℝ} (hm : 0 < m) (hb : ∀ ξ ∈ J, m ≤ (FT F ξ).re) :
    p.ν J ≤ ENNReal.ofReal (Real.pi * Arch F / m) := by
  have hw := weak_duality hp hF MeasurableSet.empty hJ le_rfl hm.le (by simp) hb
  simp only [measure_empty, mul_zero, zero_add] at hw
  have hpi := Real.pi_pos
  have e : ENNReal.ofReal (Real.pi * Arch F / m) = ENNReal.ofReal (Arch F) / ENNReal.ofReal (m / Real.pi) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  rw [e, ENNReal.le_div_iff_mul_le (Or.inl (by simp; positivity)) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  exact hw

/-- **Proposition 5.5 (low-height rigidity of every admissible pair).**  Every admissible pair `(μ, ν)`
satisfies the mass bounds of Table 2: `μ(I_k)` for the five zero-side windows, `ν([ξ_a, ξ_b])` for the
six prime-side windows, and `ν({ξ_{2.5}})`, `ν({ξ_6})`. -/
theorem prop_5_4 : ∀ p ∈ K,
    (∀ w ∈ zeroWindows, p.μ (Set.Icc (w.lo : ℝ) (w.hi : ℝ)) ≤ ENNReal.ofReal (w.bound : ℝ)) ∧
    (∀ w ∈ primeWindows, p.ν (Set.Icc (xiOf (w.lo : ℝ)) (xiOf (w.hi : ℝ))) ≤
      ENNReal.ofReal (w.bound : ℝ)) ∧
    (∀ w ∈ atomWindows, p.ν {xiOf (w.lo : ℝ)} ≤ ENNReal.ofReal (w.bound : ℝ)) := by
  intro p hp
  obtain ⟨F, hF, hA, -, hz, hpr, hat⟩ := cert_lowheight
  have hFc : F ∈ Cone := ConeOPS_subset_Cone hF
  have hA0 : 0 ≤ Arch F := weak_duality_nonneg hp hFc
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have hm : (0 : ℝ) < w.m := by
      simp only [zeroWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hlo : (0 : ℝ) < w.lo := by
      simp only [zeroWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num
    refine (zero_window_bound hFc hp hlo hm (hz w hw)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (by positivity)]
    refine le_trans hA ?_
    simp only [zeroWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · have hm : (0 : ℝ) < w.m := by
      simp only [primeWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    refine (prime_window_bound hFc hp measurableSet_Icc hm
      (fun ξ hξ => hpr w hw ξ hξ.1 hξ.2)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ hm]
    have h1 : Real.pi * Arch F ≤ 3.141593 * ((772525424595 : ℝ) / 10 ^ 36) := by
      apply mul_le_mul hpi.le hA hA0 (by norm_num)
    refine le_trans h1 ?_
    simp only [primeWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · have hm : (0 : ℝ) < w.m := by
      simp only [atomWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> norm_num
    refine (prime_window_bound hFc hp (measurableSet_singleton _) hm
      (fun ξ hξ => by rw [Set.mem_singleton_iff.mp hξ]; exact hat w hw)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ hm]
    have h1 : Real.pi * Arch F ≤ 3.141593 * ((772525424595 : ℝ) / 10 ^ 36) := by
      apply mul_le_mul hpi.le hA hA0 (by norm_num)
    refine le_trans h1 ?_
    simp only [atomWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> norm_num

/-! ## Proposition 5.10 (an unconditional lower bound for the slack) -/

/-- **Proposition 5.10, the slack bound.** From the certified pair for `𝒜_q`, `q = e^{0.02}`, with
`μ ≥ 4.71949 · 10^{-4}`: `κ* ≥ 4.71949 · 10^{-4} − 0.02/(2π) ≥ −2.7112 · 10^{-3}`. -/
theorem prop_5_8_kappa : ((-(27112 : ℝ) / 10 ^ 7 : ℝ) : EReal) ≤ kappaStar := by
  obtain ⟨p, hp, hdom⟩ := cert_lowerbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsl := slack_ge_of_dominates (homog_ArchShift _) (scalable_ConeG_ArchShift xi2 _) hp
    (by norm_num) hdom
  rw [slack_shift] at hsl
  have hk : (((471949 : ℝ) / 10 ^ 9 - (1 / 50 : ℝ) / (2 * Real.pi) : ℝ) : EReal) ≤ kappaStar := by
    rw [EReal.coe_sub]
    exact (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr hsl
  refine le_trans ?_ hk
  apply EReal.coe_le_coe_iff.mpr
  have hpi' := Real.pi_gt_d6
  have : (1 / 50 : ℝ) / (2 * Real.pi) ≤ (1 / 50 : ℝ) / (2 * 3.141592) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  have : (471949 : ℝ) / 10 ^ 9 - (1 / 50 : ℝ) / (2 * 3.141592) ≥ -(27112 : ℝ) / 10 ^ 7 := by
    norm_num
  linarith

/-- **Proposition 5.10, the conductor bound.** `q_min ≤ e^{0.02}`. -/
theorem prop_5_8_qmin : qmin ≤ Real.exp (1 / 50) := by
  obtain ⟨p, hp, -⟩ := cert_lowerbound
  have hK : (Kset (Arch_q (Real.exp (1 / 50))) xi2).Nonempty := by
    refine ⟨p, ?_⟩
    show Admissible (ArchShift (Real.log (Real.exp (1 / 50)) / (2 * Real.pi))) xi2 p
    rw [Real.log_exp]; exact hp
  exact (conductor_form (Real.exp_pos _)).mp hK

/-- **Proposition 5.10.** For `ζ`'s data with conductor `q = e^{0.02}` there is an admissible pair with
`μ ≥ 4.71949 · 10^{-4}` (ledger certificate); hence `q_min ≤ e^{0.02}` and
`κ* ≥ 4.71949 · 10^{-4} − 0.02/(2π) ≥ −2.7112 · 10^{-3}`. -/
theorem prop_5_8 :
    qmin ≤ Real.exp (1 / 50) ∧ ((-(27112 : ℝ) / 10 ^ 7 : ℝ) : EReal) ≤ kappaStar :=
  ⟨prop_5_8_qmin, prop_5_8_kappa⟩

/-! ## Proposition 5.11 (the data of ℚ(√5) and ℚ(√−3), also at their natural gaps) -/

/-- `κ*_g` for the archimedean data `𝒜_{𝔤,q}` (§5.5). -/
def kappaG (ks : List ℕ) (q g : ℝ) : EReal := slack (ArchG ks q) (ConeG g)

theorem ArchG_shift (ks : List ℕ) {q₀ q : ℝ} (_hq₀ : 0 < q₀) (_hq : 0 < q) (F : ℂ → ℂ) :
    ArchG ks q F = ArchG ks q₀ F + (Real.log q - Real.log q₀) / (2 * Real.pi) * intR F := by
  unfold ArchG
  ring

/-- Upper bounds at every gap from a dual function in `𝒞_OPS`. -/
theorem kappaG_le_of_OPS (ks : List ℕ) {q : ℝ} {F : ℂ → ℂ} (hF : F ∈ ConeOPS)
    (hpos : 0 < intR F) {b : ℝ} (hb : ArchG ks q F ≤ b * intR F) (g : ℝ) :
    kappaG ks q g ≤ (b : EReal) := by
  unfold kappaG
  have h := slack_le (homog_ArchG ks q) (scalable_ConeG_ArchG g ks q) (ConeOPS_subset_ConeG g hF) hpos
  refine h.trans ?_
  have : ArchG ks q F / intR F ≤ b := by rw [div_le_iff₀ hpos]; exact hb
  exact_mod_cast this

/-- Lower bounds at every gap `g ≤ g'` from a pair admissible at `g'` (natural-gap step), read at the
conductor `q ≥ q₀`. -/
theorem kappaG_ge_of_pair (ks : List ℕ) {q₀ q g g' c : ℝ} (hq₀ : 0 < q₀) (hq : q₀ ≤ q)
    (hc : 0 ≤ c) {p : Pair} (hp : Admissible (ArchG ks q₀) g' p) (hdom : DominatesLeb p.μ c)
    (hg : g ≤ g') :
    ((c + (Real.log q - Real.log q₀) / (2 * Real.pi) : ℝ) : EReal) ≤ kappaG ks q g := by
  have hq0 : 0 < q := lt_of_lt_of_le hq₀ hq
  set d : ℝ := (Real.log q - Real.log q₀) / (2 * Real.pi) with hd
  have hd0 : 0 ≤ d := by
    have : Real.log q₀ ≤ Real.log q := Real.log_le_log hq₀ hq
    have := Real.pi_pos
    rw [hd]; apply div_nonneg <;> linarith
  have hp' : Admissible (fun F => ArchG ks q F - d * intR F) g p := by
    have : (fun F => ArchG ks q F - d * intR F) = ArchG ks q₀ := by
      funext F; rw [ArchG_shift ks hq₀ hq0 F]; ring
    rw [this]; exact admissible_mono_gap hg hp
  have hadm := admissible_add_leb hd0 hp'
  have hdom' : DominatesLeb (p.μ + ENNReal.ofReal d • volume) (c + d) := by
    unfold DominatesLeb at hdom ⊢
    rw [ENNReal.ofReal_add hc hd0, add_smul]
    gcongr
  unfold kappaG
  exact slack_ge_of_dominates (homog_ArchG ks q) (scalable_ConeG_ArchG g ks q) hadm
    (by linarith) hdom'

theorem xiOf_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : xiOf x ≤ xiOf y := by
  unfold xiOf
  apply div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
  have := Real.pi_pos; positivity

/-- **Proposition 5.11(a).**  For the archimedean data `𝒜_{Γ_ℝ²,5}` of `ℚ(√5)` and every gap
`g ∈ (0, ξ_{4.04915}]`, in particular for `ξ₂` and for the natural gap `ξ₄`:
`1.64 · 10^{-5} ≤ κ*_g ≤ 4.83 · 10^{-4}`. -/
theorem prop_5_9_a : ∀ g : ℝ, 0 < g → g ≤ xiOf ((4049150 : ℝ) / 10 ^ 6) →
    (((164 : ℝ) / 10 ^ 7 : ℝ) : EReal) ≤ kappaG [0, 0] 5 g ∧
      kappaG [0, 0] 5 g ≤ (((483 : ℝ) / 10 ^ 6 : ℝ) : EReal) := by
  intro g _ hg
  obtain ⟨hl5, hu5⟩ := log_five_bounds
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hpi0 := Real.pi_pos
  constructor
  · obtain ⟨p, hp, hdom⟩ := cert_Qsqrt5_pair
    have hq₀ : (0 : ℝ) < Real.exp ((16093347792651136 : ℝ) / 10 ^ 16) := Real.exp_pos _
    have hqle : Real.exp ((16093347792651136 : ℝ) / 10 ^ 16) ≤ 5 := by
      rw [← Real.log_le_log_iff (Real.exp_pos _) (by norm_num), Real.log_exp]
      linarith
    have h := kappaG_ge_of_pair [0, 0] hq₀ hqle (by norm_num) hp hdom hg
    refine le_trans ?_ h
    apply EReal.coe_le_coe_iff.mpr
    rw [Real.log_exp]
    have h1 : (16094379 / 10 ^ 7 - 16093347792651136 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847)
        ≤ (Real.log 5 - 16093347792651136 / 10 ^ 16) / (2 * Real.pi) := by
      apply div_le_div₀ (by linarith) (by linarith) (by positivity) (by linarith)
    have h2 : (164 : ℝ) / 10 ^ 7 ≤ 659497 / 10 ^ 14 +
        (16094379 / 10 ^ 7 - 16093347792651136 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847) := by
      norm_num
    linarith
  · obtain ⟨F, hF, hpos, hA⟩ := cert_Qsqrt5_dual
    have hA5 : ArchG [0, 0] 5 F ≤
        ((-(25566705789831547610 : ℚ) / 10 ^ 20 : ℚ) + Real.log 5 / (2 * Real.pi)) * intR F := by
      have := ArchG_shift [0, 0] (q₀ := 1) one_pos (by norm_num : (0 : ℝ) < 5) F
      rw [Real.log_one, sub_zero] at this
      rw [this, add_mul]
      gcongr
    refine (kappaG_le_of_OPS [0, 0] hF hpos hA5 g).trans ?_
    apply EReal.coe_le_coe_iff.mpr
    have h1 : Real.log 5 / (2 * Real.pi) ≤ (16094380 / 10 ^ 7 : ℝ) / (2 * 3.14159265358979323846) := by
      apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
    have h2 : ((-(25566705789831547610 : ℚ) / 10 ^ 20 : ℚ) : ℝ) +
        (16094380 / 10 ^ 7 : ℝ) / (2 * 3.14159265358979323846) ≤ (483 : ℝ) / 10 ^ 6 := by
      push_cast; norm_num
    linarith

/-- **Proposition 5.11(b).**  For the data `𝒜_{Γ_ℂ,3}` of `ℚ(√−3)` and every gap
`g ∈ (0, ξ_{3.011664}]`, in particular for `ξ₂` and for the natural gap `ξ₃`:
`1.50 · 10^{-4} ≤ κ*_g ≤ 9.99 · 10^{-4}`. -/
theorem prop_5_9_b : ∀ g : ℝ, 0 < g → g ≤ xiOf ((3011664 : ℝ) / 10 ^ 6) →
    (((150 : ℝ) / 10 ^ 6 : ℝ) : EReal) ≤ kappaG [0, 1] 3 g ∧
      kappaG [0, 1] 3 g ≤ (((999 : ℝ) / 10 ^ 6 : ℝ) : EReal) := by
  intro g _ hg
  obtain ⟨hl3, hu3⟩ := log_three_bounds
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hpi0 := Real.pi_pos
  constructor
  · obtain ⟨p, hp, hdom⟩ := cert_Qsqrtm3_pair
    have hq₀ : (0 : ℝ) < Real.exp ((10976698108720329 : ℝ) / 10 ^ 16) := Real.exp_pos _
    have hqle : Real.exp ((10976698108720329 : ℝ) / 10 ^ 16) ≤ 3 := by
      rw [← Real.log_le_log_iff (Real.exp_pos _) (by norm_num), Real.log_exp]
      linarith
    have h := kappaG_ge_of_pair [0, 1] hq₀ hqle (by norm_num) hp hdom hg
    refine le_trans ?_ h
    apply EReal.coe_le_coe_iff.mpr
    rw [Real.log_exp]
    have h1 : (10986122 / 10 ^ 7 - 10976698108720329 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847)
        ≤ (Real.log 3 - 10976698108720329 / 10 ^ 16) / (2 * Real.pi) := by
      apply div_le_div₀ (by linarith) (by linarith) (by positivity) (by linarith)
    have h2 : (150 : ℝ) / 10 ^ 6 ≤ 667226 / 10 ^ 13 +
        (10986122 / 10 ^ 7 - 10976698108720329 / 10 ^ 16 : ℝ) / (2 * 3.14159265358979323847) := by
      norm_num
    linarith
  · obtain ⟨F, hF, hpos, hA⟩ := cert_Qsqrtm3_dual
    have hA3 : ArchG [0, 1] 3 F ≤
        ((-(17385102660887763683 : ℚ) / 10 ^ 20 : ℚ) + Real.log 3 / (2 * Real.pi)) * intR F := by
      have := ArchG_shift [0, 1] (q₀ := 1) one_pos (by norm_num : (0 : ℝ) < 3) F
      rw [Real.log_one, sub_zero] at this
      rw [this, add_mul]
      gcongr
    refine (kappaG_le_of_OPS [0, 1] hF hpos hA3 g).trans ?_
    apply EReal.coe_le_coe_iff.mpr
    have h1 : Real.log 3 / (2 * Real.pi) ≤ (10986123 / 10 ^ 7 : ℝ) / (2 * 3.14159265358979323846) := by
      apply div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
    have h2 : ((-(17385102660887763683 : ℚ) / 10 ^ 20 : ℚ) : ℝ) +
        (10986123 / 10 ^ 7 : ℝ) / (2 * 3.14159265358979323846) ≤ (999 : ℝ) / 10 ^ 6 := by
      push_cast; norm_num
    linarith

/-- The gaps named in Proposition 5.11: `ζ`'s gap `ξ₂` and the natural gaps `ξ₄`, `ξ₃` are in range. -/
theorem prop_5_9_gaps :
    0 < xi2 ∧ xi2 ≤ xiOf ((4049150 : ℝ) / 10 ^ 6) ∧ xiOf 4 ≤ xiOf ((4049150 : ℝ) / 10 ^ 6) ∧
    xi2 ≤ xiOf ((3011664 : ℝ) / 10 ^ 6) ∧ xiOf 3 ≤ xiOf ((3011664 : ℝ) / 10 ^ 6) := by
  refine ⟨?_, xiOf_mono (by norm_num) (by norm_num), xiOf_mono (by norm_num) (by norm_num),
    xiOf_mono (by norm_num) (by norm_num), xiOf_mono (by norm_num) (by norm_num)⟩
  unfold xi2 xiOf
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have := Real.pi_pos
  positivity

end PosRig
