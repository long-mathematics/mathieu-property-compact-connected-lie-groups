import MathieuProperty
import Lean.Util.CollectAxioms

/-! Audit every declaration in the mathematical project namespace, not just a
hand-picked list of theorems. This audits dependencies; manuscript coverage is
separately recorded in FORMALIZATION_STATUS.md.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`MathieuProperty).isPrefixOf name then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      match info with
      | .axiomInfo _ => throwError "Project axiom: {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"Axiom audit passed: {declarations} project declarations, {theorems} theorems."
  logInfo "All dependencies lie in {propext, Classical.choice, Quot.sound}."

#print axioms MathieuProperty.hopf_primitive_coefficient
#print axioms MathieuProperty.momentConstant_factorial
#print axioms MathieuProperty.haar_pullback
#print axioms MathieuProperty.eventual_constantTerm_zero_of_newton
#print axioms MathieuProperty.highest_weight_one_lowering
#print axioms MathieuProperty.Abelian.square_root_free_pair
#print axioms MathieuProperty.representative_algebra
#print axioms MathieuProperty.MatrixRepresentation.tensor_toMatrix
#print axioms MathieuProperty.representation_coefficient_mem
#print axioms MathieuProperty.representative_counterexample_pullback
#print axioms MathieuProperty.HasMathieuProperty.of_surjective
#print axioms MathieuProperty.hopf_integrated_coefficient
#print axioms MathieuProperty.phase_integral_constantTerm
#print axioms MathieuProperty.momentConstant_beta
#print axioms MathieuProperty.momentConstant_doubleFactorial
#print axioms MathieuProperty.Hopf.surfaceMeasure_u_zero
#print axioms MathieuProperty.Hopf.p_localization_ae
#print axioms MathieuProperty.Hopf.radial_integral_pos
#print axioms MathieuProperty.Hopf.radial_power
#print axioms MathieuProperty.Hopf.surfaceMeasure_preserving
#print axioms MathieuProperty.Hopf.hopfCoordinates_surjective
#print axioms MathieuProperty.Hopf.coordinatePoint_u
#print axioms MathieuProperty.orbit_average_integrable

#print axioms MathieuProperty.Hopf.SU2_transitive_equal_a
#print axioms MathieuProperty.Hopf.su2_orbit_map
#print axioms MathieuProperty.measurePreserving_transitive_orbit
#print axioms MathieuProperty.Hopf.radial_moment_factorization

#print axioms MathieuProperty.Hopf.mixedMoment_factorial
#print axioms MathieuProperty.Hopf.tau_polynomial_integral
#print axioms MathieuProperty.Hopf.sphere_hopf_constantTerm
#print axioms MathieuProperty.Hopf.hopf_coefficient
#print axioms MathieuProperty.Hopf.sphere_marker_tower
#print axioms MathieuProperty.Hopf.radial_transfer

#print axioms MathieuProperty.Abelian.matrix_entry_representatives
#print axioms MathieuProperty.Hopf.su2_representative_marked
#print axioms MathieuProperty.Hopf.SU2_not_mathieu

#print axioms MathieuProperty.Abelian.formal_moment_coeff
#print axioms MathieuProperty.Abelian.weighted_quadratic_substitution
#print axioms MathieuProperty.Abelian.explicit_laurent_witness

#print axioms MathieuProperty.Abelian.mixedIntegral_eq_circle_integral
#print axioms MathieuProperty.Abelian.universal_moment_conjecture_false
#print axioms MathieuProperty.Abelian.universal_convex_support_conjecture_false
#print axioms MathieuProperty.Abelian.weightedCT_growth_zero
#print axioms MathieuProperty.Abelian.universal_growth_conjecture_false

#print axioms MathieuProperty.projection_commutes
#print axioms MathieuProperty.doubletProjection_first_inner
#print axioms MathieuProperty.doubletCoordinates_equivariant
#print axioms MathieuProperty.doublet_radial_pushforward
#print axioms MathieuProperty.doubletA_ne_zero
#print axioms MathieuProperty.doublet_marked
#print axioms MathieuProperty.doublet_marked_positive
#print axioms MathieuProperty.unitary_doublet_not_mathieu

#print axioms MathieuProperty.sl2Doublet_cyclic
#print axioms MathieuProperty.sl2Doublet_irreducible
#print axioms MathieuProperty.sl2Doublet_matrix
#print axioms MathieuProperty.root_hom_injective
#print axioms MathieuProperty.specialUnitary_change_basis

#print axioms MathieuProperty.averagedInner_re_pos
#print axioms MathieuProperty.unitaryModel_intertwines
#print axioms MathieuProperty.unitaryModel_continuous
#print axioms MathieuProperty.invariantInnerProduct_invariant
#print axioms MathieuProperty.invariantInnerProduct_continuous

#print axioms MathieuProperty.center_scalar
#print axioms MathieuProperty.unitary_center_scalar
#print axioms MathieuProperty.doublet_center_invariant
#print axioms MathieuProperty.MatrixRepresentation.balanced_tensor_trivial
#print axioms MathieuProperty.MatrixRepresentation.descendedBalancedCoefficient_apply
#print axioms MathieuProperty.MatrixRepresentation.descended_hopf_functions
#print axioms MathieuProperty.center_descent

#print axioms MathieuProperty.center_quotient_tower

#print axioms MathieuProperty.beta_moment_ratio
#print axioms MathieuProperty.beta_moment_integrable
#print axioms MathieuProperty.beta_moment_product
#print axioms MathieuProperty.beta_moment_nat
#print axioms MathieuProperty.beta_two_moment
#print axioms MathieuProperty.classical_small_values
#print axioms MathieuProperty.su2_small_values

#print axioms MathieuProperty.exists_unitary_firstColumn
#print axioms MathieuProperty.exists_specialUnitary_firstColumn
#print axioms MathieuProperty.specialUnitaryRepresentation_continuous

#print axioms MathieuProperty.sphereSurface_preserving
#print axioms MathieuProperty.normalizedSphere_preserving
#print axioms MathieuProperty.specialUnitaryCompactSpace
#print axioms MathieuProperty.specialUnitarySphere_transitive
#print axioms MathieuProperty.specialUnitaryFirstColumn_map

#print axioms MathieuProperty.stdGaussian_nullSingleton
#print axioms MathieuProperty.sphereDirection_gaussian_invariant
#print axioms MathieuProperty.gaussian_sphere
#print axioms MathieuProperty.complexGaussianCoordinates_map
#print axioms MathieuProperty.normalized_independent_complex_gaussian

#print axioms MathieuProperty.gammaSplit_map
#print axioms MathieuProperty.gammaRatioSum_map
#print axioms MathieuProperty.gamma_ratio_beta
#print axioms MathieuProperty.gamma_sum_gamma

#print axioms MathieuProperty.gaussian_square_gamma
#print axioms MathieuProperty.gaussian_pair_squares_gamma

#print axioms MathieuProperty.finite_gamma_sum
#print axioms MathieuProperty.finite_gamma_ratio_beta
#print axioms MathieuProperty.complexGaussian_normSq_map
#print axioms MathieuProperty.gamma_one_scale_rate
#print axioms MathieuProperty.sphere_dirichletOne
#print axioms MathieuProperty.sphere_two_coordinates_beta
#print axioms MathieuProperty.specialUnitaryRadialA_map
#print axioms MathieuProperty.specialUnitaryRadialA_moment
#print axioms MathieuProperty.specialUnitaryRadialA_integrable

#print axioms MathieuProperty.not_mathieu_of_representative_witness
#print axioms MathieuProperty.su2Block_injective
#print axioms MathieuProperty.su2Block_continuous
#print axioms MathieuProperty.classical_representative_marked
#print axioms MathieuProperty.classical_marker_tower
#print axioms MathieuProperty.classical_marked_positive
#print axioms MathieuProperty.classical_marked_zero
#print axioms MathieuProperty.specialUnitary_not_mathieu
#print axioms MathieuProperty.specialUnitary_small_values
#print axioms MathieuProperty.specialUnitary_closed_forms

#print axioms MathieuProperty.symplecticReindex_symm_mem_specialUnitary
#print axioms MathieuProperty.compactSymplecticCompactSpace
#print axioms MathieuProperty.pairedMatrix_symplectic
#print axioms MathieuProperty.unitaryDoubleMatrix_symplectic
#print axioms MathieuProperty.exists_unitary_symplectic_firstColumn
#print axioms MathieuProperty.exists_compactSymplectic_firstColumn
#print axioms MathieuProperty.compactSymplectic_rank_one_top
#print axioms MathieuProperty.su2CompactSymplecticOne
#print axioms MathieuProperty.compactSymplecticSphere_transitive
#print axioms MathieuProperty.compactSymplecticFirstColumn_map
#print axioms MathieuProperty.compactSymplecticRadialA_map
#print axioms MathieuProperty.compactSymplecticRadialA_one
#print axioms MathieuProperty.compactSymplecticRadialA_moment
#print axioms MathieuProperty.compactSymplecticRadialA_integrable

#print axioms MathieuProperty.su2Symplectic_continuous
#print axioms MathieuProperty.su2Symplectic_injective
#print axioms MathieuProperty.symplecticProjection_equivariant
#print axioms MathieuProperty.symplectic_representative_pure
#print axioms MathieuProperty.symplectic_representative_marked
#print axioms MathieuProperty.symplectic_marker_tower
#print axioms MathieuProperty.symplectic_marked_positive
#print axioms MathieuProperty.symplectic_marked_zero
#print axioms MathieuProperty.compactSymplectic_small_values
#print axioms MathieuProperty.compactSymplectic_not_mathieu
#print axioms MathieuProperty.compactSymplectic_closed_forms

#print axioms MathieuProperty.Abelian.bernstein_integral
#print axioms MathieuProperty.Abelian.xzFamily_integrated_coeff
#print axioms MathieuProperty.Abelian.xzFamily_integral_pure
#print axioms MathieuProperty.Abelian.xzFamily_integral_marked
#print axioms MathieuProperty.Abelian.weighted_square_substitution
#print axioms MathieuProperty.Abelian.earlierXZ_specialize
#print axioms MathieuProperty.Abelian.earlierXZ_pure
#print axioms MathieuProperty.Abelian.earlierXZ_marked
#print axioms MathieuProperty.Abelian.earlierXZ_spectrum
#print axioms MathieuProperty.Abelian.weighted_xz_witness

#print axioms MathieuProperty.Hopf.sphereMonomial_integral_zero_of_unbalanced
#print axioms MathieuProperty.Hopf.spherePolynomialAlgebra_dense
#print axioms MathieuProperty.Hopf.sphere_integral_eq_of_monomials
#print axioms MathieuProperty.Hopf.sphere_measure_eq_of_monomials
#print axioms MathieuProperty.Hopf.integral_unit_phase
#print axioms MathieuProperty.Hopf.integral_unit_beta
#print axioms MathieuProperty.Hopf.hopfCoordinateMeasure_monomial_eq_surface
#print axioms MathieuProperty.Hopf.hopfCoordinateMeasure_eq_surface
#print axioms MathieuProperty.Hopf.unitHopfCoordinates_eq
#print axioms MathieuProperty.Hopf.hopf_coordinates_integral_unitCube
#print axioms MathieuProperty.Hopf.hopf_cube_change_of_variables
#print axioms MathieuProperty.Hopf.hopf_coordinates_integral

#print axioms MathieuProperty.Abelian.circle_polynomial_rescale
#print axioms MathieuProperty.Abelian.square_root_free_weighted_integral
#print axioms MathieuProperty.Abelian.integral_laurent_unit
#print axioms MathieuProperty.Abelian.laurent_eq_zero_of_circle
#print axioms MathieuProperty.Abelian.entry_polynomial_zero_complex_scale
#print axioms MathieuProperty.Abelian.entryTransform_representative_independent
#print axioms MathieuProperty.Abelian.haar_entryIntegral_eq_transformedIntegral
#print axioms MathieuProperty.Abelian.haar_invariant_entryIntegral_eq_weightedCT
#print axioms MathieuProperty.Abelian.entryTransform_pair
#print axioms MathieuProperty.Abelian.transform_correspondence

#print axioms MathieuProperty.hermitianPart_symmetric
#print axioms MathieuProperty.hermitianPart_commute
#print axioms MathieuProperty.jointEigenspaces_span
#print axioms MathieuProperty.jointEigenspace_apply
#print axioms MathieuProperty.coefficient_mem_characterSpan
#print axioms MathieuProperty.representative_eq_characterSpan
#print axioms MathieuProperty.haar_character_orthogonality
#print axioms MathieuProperty.torusPolynomialAlgebra_dense
#print axioms MathieuProperty.torus_character_exists
#print axioms MathieuProperty.torusCharacter_injective
#print axioms MathieuProperty.torus_representative_laurent
#print axioms MathieuProperty.torusCoefficientIntegral_laurent
#print axioms MathieuProperty.torus_integral_constantTerm
#print axioms MathieuProperty.torus_mathieu_iff_constantTerm
#print axioms MathieuProperty.zero_laurent_eventual
#print axioms MathieuProperty.zero_laurent_multiplier

#print axioms MathieuProperty.DvK.extendedDiscreteValuation_hasExtension
#print axioms MathieuProperty.DvK.AnnulusSeries.fixedPoint_coeff_zero
#print axioms MathieuProperty.DvK.dvkCoefficientExtraction
#print axioms MathieuProperty.one_variable_nonzero_constant_power
#print axioms MathieuProperty.duistermaat_van_der_kallen_one_variable
#print axioms MathieuProperty.one_variable_constantTerm_mathieu
#print axioms MathieuProperty.torus_one_mathieu
#print axioms MathieuProperty.circle_mathieu

#print axioms MathieuProperty.Zwart.circleEvaluation_integral
#print axioms MathieuProperty.Zwart.circleEvaluation_pow
#print axioms MathieuProperty.Zwart.circleEvaluation_injective
#print axioms MathieuProperty.Zwart.embed_admissible
#print axioms MathieuProperty.Zwart.product_weight_moments
#print axioms MathieuProperty.Zwart.product_convexSupport_false
#print axioms MathieuProperty.Zwart.mem_radialAlgebra_iff
#print axioms MathieuProperty.Zwart.cube_integral_first
#print axioms MathieuProperty.Zwart.cube_weight_moments
#print axioms MathieuProperty.Zwart.cube_convexSupport_false
#print axioms MathieuProperty.Zwart.sunRadialCount_eq
#print axioms MathieuProperty.Zwart.sunLaurentCount_eq
#print axioms MathieuProperty.Zwart.sunDensity_eq
#print axioms MathieuProperty.Zwart.sun_conjecture_2025_false
#print axioms MathieuProperty.Zwart.sun_reduction_2025

-- Restricted radial domains and the exact G2 nested integral.
#print axioms MathieuProperty.Zwart.continuous_circleEvaluation
#print axioms MathieuProperty.Zwart.weightedMoment_circles_outer
#print axioms MathieuProperty.Zwart.weightedMoment_restrict
#print axioms MathieuProperty.Zwart.cube_restricted_convexSupport_false
#print axioms MathieuProperty.Zwart.cube_integral_last_restrict
#print axioms MathieuProperty.Zwart.g2Boundary_sin
#print axioms MathieuProperty.Zwart.g2_conjecture_2025_false
#print axioms MathieuProperty.Zwart.g2_weightedMoment_nested
#print axioms MathieuProperty.Zwart.g2_conjecture_2025_nested_false
