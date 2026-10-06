import PositivityRigidity
/-! `#print axioms` for the headline theorems (Theorems A, B, C, D, the Corollary, the logic of §1.2) and
for every other formalised numbered statement (v1.1 numbering).  Output: `axioms.log`
(`lake env lean scripts/print_axioms.lean > axioms.log`); `scripts/audit.sh` requires the output to equal
`axioms.log` exactly. -/
-- Headline results (§1), v1.0 names (unchanged)
#print axioms PosRig.theoremA
#print axioms PosRig.logic_display
#print axioms PosRig.theoremB'
#print axioms PosRig.corollary_magic
#print axioms PosRig.theoremC
#print axioms PosRig.theoremD'
#print axioms PosRig.conjS_equivalences
-- Headline results (§1), added in v1.1
#print axioms PosRig.theoremB_a
#print axioms PosRig.theoremB_b
#print axioms PosRig.corollary_magic_a
#print axioms PosRig.theoremD_nonstrict'
-- §2
#print axioms PosRig.Gset_inTδ
#print axioms PosRig.Admissible.isLocallyFinite
#print axioms PosRig.weak_duality
#print axioms PosRig.not_dominatesLeb_of_cone
#print axioms PosRig.duality
#print axioms PosRig.K_convex
#print axioms PosRig.prop_2_8
#print axioms PosRig.duality_no_gap_hyp_of_ge
#print axioms PosRig.exists_admissible_shift
#print axioms PosRig.prop_2_8_dominates
#print axioms PosRig.logic_a
#print axioms PosRig.logic_c
#print axioms PosRig.logic_d
#print axioms PosRig.conductor_form
#print axioms PosRig.qmin_le_one_of_RH
#print axioms PosRig.criticality
#print axioms PosRig.criticality_c
#print axioms PosRig.comp_slackness
-- §3
#print axioms PosRig.support_uniqueness_thm
#print axioms PosRig.prop_3_5
#print axioms PosRig.prop_3_5_strong
#print axioms PosRig.zero_support_theorem
#print axioms PosRig.zero_support_rigidity_sanity
#print axioms PosRig.thm_3_7
#print axioms PosRig.thm_3_7_admissible
#print axioms PosRig.extra_zeros_countable
#print axioms PosRig.extra_zeros_countable_admissible
#print axioms PosRig.theoremB_b_countable
#print axioms PosRig.theoremB_finite_of_countable
#print axioms PosRig.cumulativeCond_of_weightedCond
#print axioms PosRig.weightedCond_of_finite
#print axioms PosRig.magic_function_principle
#print axioms PosRig.magic_principle_zero
#print axioms PosRig.condU_iff_carriedBy
#print axioms PosRig.condU_iff_Xi_sq
#print axioms PosRig.carriedBy_Zzeta_of_lintegral
#print axioms PosRig.carriedBy_Zzeta_of_integral
#print axioms PosRig.isClosed_Zzeta
-- §4
#print axioms PosRig.zero_killing_EF
#print axioms PosRig.FT_Ffam_pp
#print axioms PosRig.deriv_FT_Ffam_pp
#print axioms PosRig.Ffam_mem_TestClass
#print axioms PosRig.Xi_sq_mem_TestClass
#print axioms PosRig.Arch_Ffam_tail
#print axioms PosRig.Arch_nonneg_of_zero_killing
#print axioms PosRig.theoremD
#print axioms PosRig.theoremD_nonstrict
#print axioms PosRig.hypMg0_of_hypMg
#print axioms PosRig.coeff_bound_consequences
#print axioms PosRig.remark_4_10a
#print axioms PosRig.remark_4_10a_nonstrict
#print axioms PosRig.remark_4_10b
#print axioms PosRig.remark_4_10b_zero
#print axioms PosRig.certificate_route
-- §5
#print axioms PosRig.thm_5_1
#print axioms PosRig.cor_5_2
#print axioms PosRig.cor_5_2_RH
#print axioms PosRig.near_rigidity
#print axioms PosRig.near_rigidity_interval
#print axioms PosRig.Frep_ge_Xi_sq
#print axioms PosRig.prop_5_3
#print axioms PosRig.prop_5_4
#print axioms PosRig.prop_5_5
#print axioms PosRig.prop_5_8
#print axioms PosRig.prop_5_9_a
#print axioms PosRig.prop_5_9_b
#print axioms PosRig.prop_5_9_not_singleton
-- §6, Appendix A
#print axioms PosRig.conjFamily_implies
#print axioms PosRig.conjFamily0_implies
#print axioms PosRig.conjFamily0_of_conjFamily
#print axioms PosRig.posc_a
#print axioms PosRig.posc_b'
-- Faithfulness checks and the cross-check of the explicit-formula axiom
#print axioms PosRig.TestClass.Arch_eq_paper
#print axioms PosRig.RH_iff_critical
#print axioms PosRig.explicit_formula_of_paleyWiener
#print axioms PosRig.paperFT_mem_TestClass
