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
