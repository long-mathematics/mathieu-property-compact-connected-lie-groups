# Formalization status

## Scope and integrity

Source of truth: `mathieu_property_compact_connected_lie_groups.tex` at initial commit `aa283858550cc73fd9e06d34a40d111d2ad8b2d0`.
The manuscript is unchanged. This ledger records obligations, not assertions of completion.
`PROVED` means the full stated obligation has been checked by Lean without placeholders.
Definitions use `PROVED` only after their implementation and stated correspondence are checked.
Every Lean name below is intended until linked to an actual checked declaration.
All modules are under `MathieuProperty/`; names are in namespace `MathieuProperty`.
Rows for external results are obligations to prove or reuse mathlib, never licenses to assume them.

## Current state

- Development branch: `formalization/abelian-weighted-moments`; prior foundation milestone [PR #1](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/1). Use `git status` for the live checkout after merging.
- Lean: `leanprover/lean4:v4.34.0`.
- mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0).
- M0 and M1 complete; the library covers 31 mathematical modules plus the import umbrella. The Hopf coefficient theorem, sphere marker tower, and universal radial-transfer theorem are proved, as are the representative-algebra and Haar-pullback lemmas. The main classification, uniform nonabelian tower, root subgroup existence, and torus direction remain outstanding. The exact Hopf coordinate-density obligation H05 remains open; the sphere theorem uses a documented invariant-moment proof instead.
- Completion is prevented by the documented library exception below, independently of the many remaining ordinary obligations. The checked foundations are preserved through PR #1; remote validation and merge state are available there. No weakening or conditional main theorem is authorized.
- No false manuscript statement identified. Library exception under attached prompt §16: the rank-two Duistermaat–van der Kallen noncancellation step remains unproved after the searches and proof attempts below. The known general proof would require major new toric/analytic infrastructure, which is not realistically achievable as a routine continuation of this paper formalization. The foundation milestone is incomplete coverage, not a completed formalization.

## Dependency order

1. M0: pinned project, this ledger, library search.
2. M1: definitions, representative algebra, Haar pullback.
3. M2: Hopf relation, phase balance, homogeneity, transformed identities.
4. M3: primitive coefficient congruence → sphere measure/phase extraction → Hopf identity → Pascal tower.
5. M4: SU(2) sphere orbits and measure averaging → radial transfer.
6. M5: fundamental representation → root doublet → projected Haar → simple-group theorem and classical examples.
7. M6: Schur and tensor descent → all compact simple central forms.
8. M7: compact Lie algebra structure → adjoint simple quotient → uniform nonabelian theorem.
9. M8: torus/characters/Laurent correspondence + Duistermaat–van der Kallen → torus Mathieu property.
10. M9: M7 + M8 + abelian iff torus → classification.
11. M10: exact transformed witness, admissibility and external abelian reductions.
12. M11: manuscript correspondence, clean build, axiom audit, CI, final publication.

## Exhaustive working inventory

Ranges in dependencies refer to all numbered rows in that range. If a proof exposes further intermediate assertions they must be added before being counted as covered.

| Manuscript label / obligation | Mathematical statement | Intended Lean declaration | Module | Dependencies | Status | Proof route | Library issue |
|---|---|---|---|---|---|---|---|
| def:mathieu-subspace | Positive powers in a subspace imply eventual membership after each fixed multiplier | IsMathieuSubspace | Basic |  | PROVED | Manuscript |  |
| lem:representative-algebra | Unital star algebra; tensor/conjugate coefficients; continuous pullback | representative_algebra; MatrixRepresentation.coefficient_mul; MatrixRepresentation.coefficient_conj; representative_comp | RepresentativeFunctions | D-representative; U-tensor; U-conjugate | PROVED | Coordinate model, with formal basis/tensor correspondence | Exact finite span equals the constructed star algebra; arbitrary finite-dimensional representation coefficients included. |
| lem:haar-pullback | Surjective continuous homomorphisms preserve normalized Haar integrals and counterexamples | map_normalizedHaar; haar_pullback; representative_counterexample_pullback; HasMathieuProperty.of_surjective | Haar / Basic | D-haar; U-haar-map; U-counterexample-pullback | PROVED | Manuscript | Normalized Haar identity and pullback on the actual representative algebra; no residual closure assumptions. |
| thm:hopf-coefficient | Sphere integral H(q)p^m = c_m times coefficient m of H(X)(1+X)^(m-1), m≥1 | Hopf.hopf_coefficient | HopfIntegral | H01–H04; H06–H12; H15–H19 | PROVED | Substitute for coordinate density: invariant mixed moments, then manuscript phase/primitive calculation | Actual normalized Euclidean surface measure; all complex H and positive m; no extra mathematical assumptions. |
| cor:sphere-marker-tower | Pure moments zero; all marked moments, vanishing/strict positivity ranges | Hopf.sphere_marker_tower | HopfIntegral | thm:hopf-coefficient; H13; H14 | PROVED | Manuscript | Complex positivity is stated as equality to a strictly positive real number. |
| thm:radial-transfer | All finite compactly supported positive SU(2)-invariant measures: pure and marked formulas with radial power and positivity | Hopf.radial_transfer | RadialTransfer | R01–R08; cor:sphere-marker-tower | PROVED | Manuscript | Actual defining SU(2) action, every finite Borel measure with compact support and action invariance, including zero measure and origin mass. |
| lem:root-doublet | Fundamental highest-weight representation contains a faithful defining SU(2) root doublet | highest_weight_one_lowering | RootDoubletAlgebra / RootSU2 (planned) | L01–L07 | IN PROGRESS | Manuscript | Only its algebraic lowering step is checked. Fundamental representation and root integration are absent. |
| lem:radial-pushforward | Projected Haar is compactly supported invariant probability, not concentrated at zero | radial_pushforward | SimpleGroups | lem:root-doublet; L08–L11 | TODO | Manuscript |  |
| thm:simply-connected-simple | Representative A,P,Q, nonnegative nonzero A, exact tower on all compact simply connected simple groups | simply_connected_simple | SimpleGroups | lem:radial-pushforward; thm:radial-transfer; lem:representative-algebra | TODO | Manuscript |  |
| prop:classical-closed-forms | Defining SU(n), n≥2, and Sp(n), n≥1: rising factorial formulas and printed examples | classical_closed_forms | ClassicalGroups | C01–C07; thm:simply-connected-simple | TODO | Manuscript |  |
| lem:center-descent | Six functions descend as representative functions through full center and intermediate quotients | center_descent | CenterDescent | Z01–Z04; H04 | TODO | Manuscript |  |
| cor:simple-central-forms | Exact marker tower and Mathieu failure for every compact connected simple central form | simple_central_forms | CenterDescent | Z05; lem:center-descent; lem:haar-pullback; thm:simply-connected-simple | TODO | Manuscript |  |
| prop:adjoint-simple-quotient | Every nonabelian compact connected Lie group surjects continuously onto adjoint compact simple group | adjoint_simple_quotient | AdjointQuotient | G01–G06 | TODO | Manuscript |  |
| thm:uniform-nonabelian | Full manuscript quantifiers, representative triple and radial moment tower, positivity and vanishing | uniform_nonabelian | MainTheorem | prop:adjoint-simple-quotient; cor:simple-central-forms; lem:haar-pullback | TODO | Manuscript |  |
| thm:dvdk | Nonzero complex multivariate Laurent f with all positive-power constant terms zero has Newton polytope avoiding zero | duistermaat_van_der_kallen | Torus | T04 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| cor:torus | Every torus has the Mathieu property | torus_mathieu | Torus | T01–T08; thm:dvdk | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| thm:classification | For every compact connected Lie group: Mathieu property iff abelian iff torus | classification | MainTheorem | thm:uniform-nonabelian; cor:torus; T01 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| prop:explicit-abelian-SU2 | Transformed Laurent pair: exact moments, printed expansion, exact spectrum | Abelian.formal_expansion; Abelian.formal_spectrum | AbelianAlgebra / AbelianLaurent | E01–E09; thm:hopf-coefficient | IN PROGRESS | Manuscript | Algebra, spectrum, and exact weighted moment formulas checked; external transform correspondence pending. |
| cor:abelian-reductions | Failure of both universal abelian conjectures, growth claim and specified Zwart reductions | abelian_reductions | AbelianWitness | E10–E14; prop:explicit-abelian-SU2; thm:classification | TODO | Manuscript |  |
| D-representative | Finite linear combinations of coefficients of finite-dimensional continuous complex representations | representativeFunctions; representative_eq_span_coefficients; representation_coefficient_mem | RepresentativeFunctions |  | PROVED | Coordinate model, with formal basis correspondence | Finite linear span, without topological closure; arbitrary finite-dimensional normed complex representation spaces and joint continuity checked. |
| D-haar | Normalized Haar integration on representative functions | normalizedHaar; representativeIntegral; representativeIntegral_one | Haar | D-representative | PROVED | Manuscript | Linear restriction to the representative algebra; integrability and normalization proved. |
| D-property | Mathieu property is Mathieu condition on the kernel of Haar integral | HasMathieuProperty | Haar | D-haar; def:mathieu-subspace | PROVED | Manuscript | Mathieu condition on the kernel of representativeIntegral. |
| D-hopf | a, τ, u, v, universal P,Q, sphere restrictions p,q | Hopf.a; Hopf.tau; Hopf.u; Hopf.v; Hopf.P; Hopf.Q; Hopf.Sphere; Hopf.p; Hopf.q | HopfAlgebra |  | PROVED | Manuscript |  |
| D-cm | Integral c_m and factorial/beta/double-factorial alternatives | momentConstant; momentConstant_factorial; momentConstant_beta; momentConstant_doubleFactorial | MomentConstant |  | PROVED | Substitute: integration recurrence and mathlib beta integral | All printed forms and positivity checked; beta equality uses the complex-valued Euler integral at positive real arguments. |
| D-CT | Coefficient and Laurent constant term conventions; negative coefficients zero | MultiLaurent; constantTerm; newtonPolytope | LaurentSupport |  | PROVED | Manuscript | AddMonoidAlgebra on Fin d → ℤ; coefficients include cancellation. |
| D-Phi | Orthogonal projection coordinates and group A,P,Q | projectionCoordinates | SimpleGroups | L08 | TODO | Manuscript |  |
| D-explicit | U,V,T, transformed P_ab,Q_ab and matrix-entry representatives | Abelian.U; Abelian.V; Abelian.T; Abelian.P; Abelian.Q; Abelian.A₀; Abelian.U₀; Abelian.V₀; Abelian.T₀; Abelian.entryP; Abelian.formalP; Abelian.formalQ | AbelianAlgebra / AbelianLaurent |  | PROVED | Manuscript | The formal algebra is ℂ[x][w,w⁻¹]. |
| U-tensor | Product of coefficients is a tensor-product coefficient | MatrixRepresentation.coefficient_mul; MatrixRepresentation.tensor_toMatrix | RepresentativeFunctions | D-representative | PROVED | Coordinate tensor model | Kronecker matrices identified with mathlib Representation.tprod in the tensor basis. |
| U-conjugate | Conjugate coefficient uses conjugate continuous representation | MatrixRepresentation.coefficient_conj; MatrixRepresentation.conjugate_action | RepresentativeFunctions | D-representative | PROVED | Coordinate conjugate model | Entrywise conjugation, including the action and arbitrary covectors/vectors. |
| U-haar-map | Pushforward Haar: probability, left invariance and uniqueness | map_normalizedHaar | Haar | D-haar | PROVED | Manuscript | Uses normalizedHaar, whose mass-one and Haar instances are proved. |
| U-counterexample-pullback | Power and multiplier identities preserved under algebra homomorphism with functional compatibility | counterexample_pullback | Basic | def:mathieu-subspace | PROVED | Manuscript |  |
| U-not-mathieu | A fixed witness with all pure powers inside and all marked powers outside refutes Mathieu | not_isMathieuSubspace_of_witness | Basic | def:mathieu-subspace | PROVED | Manuscript |  |
| H01 | Hopf relation a²=uv+τ² | Hopf.relation | HopfAlgebra | D-hopf | PROVED | Manuscript |  |
| H02 | Global defect-one identity, without dividing by u | Hopf.defect_one | HopfAlgebra | H01 | PROVED | Manuscript |  |
| H03 | Real homogeneity P(rz)=r⁸P(z), Q(rz)=r²Q(z) | Hopf.homogeneity | HopfAlgebra | D-hopf | PROVED | Manuscript |  |
| H04 | Common unit phase invariance of a,τ,u,v,P,Q | Hopf.phase_balance | HopfAlgebra | D-hopf | PROVED | Manuscript |  |
| H05 | Hopf-coordinate normalized surface measure, endpoints null | Hopf.hopfCoordinates; Hopf.coordinatePoint_u; Hopf.hopfCoordinates_surjective; Hopf.surfaceMeasure | SphereMeasure / HopfCoordinates / HopfIntegral (planned) | D-hopf | IN PROGRESS | Euclidean cone surface measure and explicit coordinates | Normalized surface probability, null endpoint circles, continuous surjective coordinates, and exact a, τ, u formulas proved. Exact coordinate measure density still open. |
| H06 | Normalized phase integral extracts every Laurent constant term at nonzero radius | phase_integral_constantTerm; laurentPhase_eq_smeval | PhaseAverage | D-CT | PROVED | Manuscript | All integer exponents, exact 1/(2π) normalization, agreement with Laurent evaluation at every nonzero radius. |
| H07 | Sphere polynomial integrability and justified localization away from u=0 | Hopf.sphere_polynomial_integrable; Hopf.p_localization_ae | SphereMeasure | H05 | PROVED | Manuscript | All complex polynomial moments integrable for every finite sphere measure; actual normalized surface measure has u≠0 almost everywhere, with the rational identity proved there. |
| H08 | Evenness in t and Fubini give CT-step with correct normalization | Hopf.sphere_phase_average; Hopf.sphere_hopf_constantTerm; Hopf.sphere_hopf_real_integral | SpherePhaseAverage / HopfIntegral | H06–H07; H02; H15–H19 | PROVED | Invariant polynomial marginal substitutes for coordinate density | Phase Fubini justified by compact integrability; localization only away from the proved null set; exact normalization and evenness. |
| H09 | Polynomial primitive J_m; substitution identity | hopfPrimitive_eval_integral; hopfPrimitive_complex_substitution | HopfCoefficient / HopfIntegralKernel |  | PROVED | Substitute: complex FTC and finite binomial sums | Primitive evaluated at every real endpoint; complex substitution including zero parameter proved. |
| H10 | J_m(1+X)-J_m(1) divisible by X^(m+1) | primitive_congruence | HopfCoefficient | H09 | PROVED | Manuscript |  |
| H11 | Multiplication by polynomials cannot change coefficient m of X^(m+1) multiple | coefficient_congruence | HopfCoefficient | H10 | PROVED | Manuscript |  |
| H12 | Integral c_m equals factorial ratio, beta and double factorial expressions; positive | momentConstant_factorial; momentConstant_beta; momentConstant_doubleFactorial; momentConstant_pos | MomentConstant | D-cm | PROVED | Substitute: integration recurrence and mathlib beta integral | Integral, factorial, double-factorial, and beta forms all proved. |
| H13 | Coefficient m of X^s(1+X)^(m-1) is choose(m-1,s-1), including s>m | pascal_coefficient | HopfCoefficient |  | PROVED | Manuscript |  |
| H14 | Unmarked coefficient zero; binomial positive iff 1≤s≤m | pure_pascal_coefficient; pascal_marker_pos; pascal_marker_zero | HopfCoefficient / MomentConstant | H13 | PROVED | Manuscript | Includes every positive/vanishing index range. |
| H15 | Nonzero phase-weight coordinate monomials have zero sphere integral, also after scaled SU(2) transformations | Hopf.sphereMonomial_integral_zero; Hopf.coordinateMonomial_scaled_integral_zero | SphereMonomials | R01–R02; H04 | PROVED | Substitute proof for polynomial sphere moments | Explicit diagonal SU(2) phases; a nontrivial character forces its integral to vanish. |
| H16 | Rotation and unit-norm recurrences for mixed squared-coordinate moments | Hopf.mixedMoment_balance; Hopf.mixedMoment_partition; Hopf.mixedMoment_succ_left; Hopf.mixedMoment_succ_right | SphereMomentRecurrence | H15; H19 | PROVED | Substitute proof | Coefficient one of a polynomial identity; finite sums, no differentiation under an integral. |
| H17 | Mixed moments equal p!q!/(p+q+1)! | Hopf.mixedMoment_factorial | SphereMomentRecurrence | H16 | PROVED | Substitute proof | Induction from probability normalization and the two proved recurrences. |
| H18 | Squared first coordinate is uniform on [0,1], and τ on [-1,1], for every complex polynomial test function | Hopf.firstCoordinate_polynomial_integral; Hopf.tau_polynomial_integral | SphereMarginal | H17 | PROVED | Substitute proof | Polynomial induction and affine change of variables; no full measure-density claim. |
| H19 | Integration of continuous-function polynomial coefficients commutes with evaluation; real-parameter vanishing forces the coefficient polynomial to vanish | Hopf.integrateCoefficients_coeff; Hopf.integrateCoefficients_eval; Hopf.integrateCoefficients_eq_zero | PolynomialIntegral | SphereMeasure | PROVED | Finite sums and infinitely many roots | Integrability follows from compactness. |
| R01 | Explicit SU(2) matrix proves transitivity on each nonzero sphere | Hopf.SU2_transitive_sphere; Hopf.SU2_transitive_equal_a | SU2Action / SU2Orbit |  | PROVED | Manuscript | Actual determinant-one unitary matrices; continuous defining action, sphere homeomorphism, and transitivity on every level of a. |
| R02 | Orbit Haar pushforward equals normalized surface measure | Hopf.su2_orbit_map; Hopf.su2_orbit_integral | SphereSymmetry / SU2Action / SU2Orbit / OrbitMeasure | R01; D-haar | PROVED | Invariant surface measure and Tonelli | Actual SU(2) action preserves Euclidean surface measure; transitivity and right Haar invariance identify every unit-sphere orbit pushforward. |
| R03 | Invariant-measure orbit averaging for integrable functions, product measurability and integrability | measurePreserving_smul_prod; orbit_average_integrable; integrable_orbit_function | OrbitAverage | D-haar | PROVED | Manuscript | Every integrable complex function under a continuous compact-group action with invariant finite Borel measure; product integrability is derived from invariance. Includes the continuous compact-support case. |
| R04 | Compact support gives integrability of all polynomial moments | Hopf.integrable_polynomial_compactSupport | SphereMeasure | D-hopf | PROVED | Manuscript | Finite Borel measures on ℂ² with compact support; general continuous integrands covered too. |
| R05 | Radial reduction r^(8m+2s)=a^(4m+s), including zero vector | Hopf.radial_power; Hopf.radial_real_exponent | SphereMeasure | H03 | PROVED | Manuscript | Exact exponent and sphere scaling for all scalars, including zero. |
| R06 | Pure orbit moments vanish at every vector | Hopf.orbit_pure | RadialTransfer | R02; R05; cor:sphere-marker-tower | PROVED | Manuscript | Includes zero. |
| R07 | Marked orbit moment formula at every vector | Hopf.orbit_marked | RadialTransfer | R02; R05; cor:sphere-marker-tower | PROVED | Manuscript | Exact coefficient and radial power, including zero. |
| R08 | Positive measure off zero implies positive radial integral | Hopf.radial_integral_pos | SphereMeasure | R04 | PROVED | Manuscript | Every positive natural radial power has positive integral for a finite compactly supported measure with positive mass off zero. |
| L01 | Maximal torus, simple roots and fundamental weight with coroot pairing one | fundamental_weight_pairing | RootSU2 |  | TODO | Manuscript |  |
| L02 | Simply connected compact simple group admits irreducible representation of fundamental highest weight | fundamental_representation_exists | RootSU2 | L01 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| L03 | Average inner product to obtain invariant Hermitian metric | invariant_inner_product | RootSU2 | D-haar | TODO | Manuscript |  |
| L04 | Root sl₂ action on highest vector has weight one | root_highest_weight_one | RootSU2 | L01; L02 | TODO | Manuscript |  |
| L05 | Highest-weight-one cyclic module: Fv≠0, F²v=0 and two-dimensional defining action | highest_weight_one_lowering | RootDoubletAlgebra | L04 | IN PROGRESS | Manuscript | Both lowering identities proved from a primitive weight-one vector; invariant module equivalence still pending. |
| L06 | Integrate compact root Lie algebra to SU(2) homomorphism and identify restricted representation | integrate_root_SU2 | RootSU2 | L04; L05 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| L07 | Faithfulness implies injective root map; orthonormal identification gives defining SU(2) action | root_map_injective | RootSU2 | L06 | TODO | Manuscript |  |
| L08 | Invariant orthogonal complement and equivariant projection | projection_commutes | SimpleGroups | L03; lem:root-doublet | TODO | Manuscript |  |
| L09 | Phi continuous, equivariant, norm≤1, Phi(1)=e₀ | projection_map_properties | SimpleGroups | L08 | TODO | Manuscript |  |
| L10 | Haar pushforward invariant probability supported in compact ball | projection_measure_properties | SimpleGroups | L09; U-haar-map | TODO | Manuscript |  |
| L11 | Nonempty open sets have positive Haar; continuity gives nonconcentration | projection_nonconcentration | SimpleGroups | L09; D-haar | TODO | Manuscript |  |
| C01 | First column Haar on SU(n) is uniform complex unit sphere | SU_column_uniform | ClassicalGroups |  | TODO | Manuscript |  |
| C02 | Complex Gaussian normalization produces sphere measure | gaussian_sphere | ClassicalGroups |  | TODO | Manuscript |  |
| C03 | Squared coordinate norms are Dirichlet(1,…,1), first two sum Beta(2,n-2) | sphere_two_coordinates_beta | ClassicalGroups | C02 | TODO | Manuscript |  |
| C04 | Beta moments equal rising factorial ratios | beta_moment | ClassicalGroups | C03 | TODO | Manuscript |  |
| C05 | Sp(n) defining action transitive on complex 2n sphere with same invariant measure | Sp_sphere_transitive | ClassicalGroups |  | TODO | Manuscript |  |
| C06 | Endpoint n=2 for SU and n=1 for Sp: A=1 and ratio=1 | classical_endpoints | ClassicalGroups | C01; C05 | TODO | Manuscript |  |
| C07 | Nine rational examples for m=1,2,3 | classical_small_values | ClassicalGroups | C04; H12 | TODO | Manuscript |  |
| Z01 | Schur lemma: center acts by scalar of modulus one | center_scalar | CenterDescent | L02; L03 | TODO | Manuscript |  |
| Z02 | Balanced coefficients invariant; tensor representation has trivial central action | balanced_center_trivial | CenterDescent | Z01; H04 | TODO | Manuscript |  |
| Z03 | Tensor conjugate representation factors continuously through central quotient | tensor_factors_quotient | CenterDescent | Z02 | TODO | Manuscript |  |
| Z04 | All six functions are coefficients of sums/tensor powers on quotient | descended_representative | CenterDescent | Z03; lem:representative-algebra | TODO | Manuscript |  |
| Z05 | Any compact connected simple central form is central quotient of compact simply connected simple cover | simple_cover | CenterDescent |  | TODO | Manuscript |  |
| G01 | Compact Lie algebra decomposes as center plus simple ideals | compact_lie_decomposition | AdjointQuotient |  | TODO | Manuscript |  |
| G02 | Connected nonabelian group has at least one simple ideal | nonabelian_simple_ideal | AdjointQuotient | G01 | TODO | Manuscript |  |
| G03 | Connected adjoint action preserves each simple ideal | adjoint_preserves_simple_ideal | AdjointQuotient | G01 | TODO | Manuscript |  |
| G04 | Inner automorphism group is compact connected adjoint simple; automorphism identity component | inner_aut_structure | AdjointQuotient | G01 | TODO | Manuscript |  |
| G05 | Restricted adjoint differential image equals ad(simple ideal) | restricted_adjoint_differential | AdjointQuotient | G01; G03 | TODO | Manuscript |  |
| G06 | Closed connected subgroup with full Lie algebra equals connected target | full_lie_algebra_surjective | AdjointQuotient | G04; G05 | TODO | Manuscript |  |
| T01 | Compact connected abelian Lie group iff finite-dimensional torus, including dimension zero | abelian_iff_torus | Torus |  | TODO | Manuscript |  |
| T02 | Character lattice of torus is Z^d and representatives are finite character sums | torus_representative_laurent | Torus | T01; D-representative | TODO | Manuscript |  |
| T03 | Normalized Haar integral corresponds to Laurent coefficient at zero | torus_integral_constantTerm | Torus | T02; D-haar | TODO | Manuscript |  |
| T04 | Duistermaat–van der Kallen external result must be proved, not postulated | dvdk_external_proof | Torus |  | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| T05 | Strict linear separation from convex hull of finite support | support_strict_separation | LaurentSupport | thm:dvdk | PROVED | Manuscript | Mathlib geometric Hahn–Banach and compactness of finite convex hull. |
| T06 | Support of hf^m has separating-functional value≥C+mδ | support_mul_lower_bound; support_pow_lower_bound | LaurentSupport | T05 | PROVED | Manuscript | Support containment, not an incorrect equality of supports. |
| T07 | Archimedean bound yields eventual absence of zero exponent | eventual_constantTerm_zero_of_lower_bound; eventual_constantTerm_zero_of_newton | LaurentSupport | T06 | PROVED | Manuscript | Zero polynomials allowed; all natural m above N. |
| T08 | Zero f/h cases and equivalence with Mathieu subspace on torus | torus_zero_cases | Torus | T02; T03; T07 | TODO | Manuscript |  |
| E01 | U V + T² = 1 | Abelian.relation | AbelianAlgebra | D-explicit | PROVED | Manuscript | General commutative ring proof with w*wi=1; applies to unit-circle w. |
| E02 | Defect-one transformed identity | Abelian.defect_one | AbelianAlgebra | E01 | PROVED | Manuscript | Global polynomial identity; no division used. |
| E03 | Printed Laurent expansion exactly equal to P_ab | Abelian.expansion; Abelian.formal_expansion | AbelianAlgebra / AbelianLaurent | D-explicit | PROVED | Manuscript | Also equality in the actual Laurent polynomial algebra. |
| E04 | Four nonzero coefficient polynomials give exact formal spectrum {-1,0,1,2} | Abelian.formal_spectrum | AbelianLaurent | E03 | PROVED | Manuscript | All four coefficient polynomials proved nonzero by evaluation; no claim of fixed-x endpoint spectrum. |
| E05 | t=1-2x² gives normalized weighted CT integral and moment laws | Abelian.weighted_quadratic_substitution; Abelian.weightedCT_pure; Abelian.weightedCT_marked | AbelianConstantTerm / AbelianWitness | E02; H08 | PROVED | Manuscript | Actual formal Laurent coefficients, exact weight and normalization, every positive power and marker; positivity and vanishing ranges also proved. |
| E06 | On SU(2), conjugate entry identities give polynomial Hopf representatives | Abelian.matrix_entry_representatives; Abelian.matrix_entry_pair | SU2Witness | D-hopf; R01 | PROVED | Manuscript | Exact four-entry polynomial formulas; the pair is also constructed in the actual representative algebra. |
| E07 | All entry representatives invariant under maximal torus factor | Abelian.torus_invariance; Abelian.entryP_torus_invariance | AbelianAlgebra | E06 | PROVED | Manuscript | U₀ is also the Q entry representative. |
| E08 | Square-root-free substitution sends A₀,U₀,V₀,T₀ to 1,U,V,T | Abelian.square_root_free; Abelian.square_root_free_pair | AbelianAlgebra | E06 | PROVED | Manuscript | All complex x and nonzero w, including manuscript domain. |
| E09 | Representative independence and equality to actual Mueger–Tuset group-coordinate transform | Abelian.transform_correspondence | AbelianWitness | E07; E08; E14 | TODO | Manuscript |  |
| E10 | Earlier weighted xz witness has zero pure moments and (-1)^(m-1)/(2(m+1)) marker; spectrum {-1,0,1} | weighted_xz_witness | AbelianWitness |  | TODO | Manuscript |  |
| E11 | Definitions and admissibility of universal moment and convex-support conjectures | universal_abelian_conjectures | AbelianWitness | E14 | TODO | Manuscript |  |
| E12 | Zero pure moment sequence has zero limsup growth, contradicting asserted positive growth | growth_counterexample | AbelianWitness | E11; prop:explicit-abelian-SU2 | TODO | Manuscript |  |
| E13 | Each specified Zwart abelian implication formally stated and proved, then contraposition | zwart_reductions_false | AbelianWitness | E14; thm:classification | TODO | Manuscript |  |
| E14 | External Mueger–Tuset Lemma 5.2, Prop 5.3, Conjectures 6.3/6.6, Remark 6.7; Zwart implications: exact definitions and needed results | external_reduction_correspondence | AbelianWitness |  | TODO | Manuscript |  |

## Expository exclusions

Historical claims in the introduction about the Jacobian conjecture, announcements, and prior projects are not used by the direct classification proof and are excluded. The indirect first paragraph of the abelian-reductions section is likewise excluded; the direct witnesses and named failure corollary remain in scope. Remarks “Defect-one coefficient law”, “Strength of the failure”, “No classification by Lie type”, and “Scope” restate conclusions or delimit scope. The mixed-case remark's admissibility/unused-variable observation is included in E09/E11. No named theorem, lemma, proposition, corollary, or definition is excluded.

## Library search and external-result log

- Initial whole-mathlib search for `duistermaat`, `van.der.kallen`, and mathematical `Mathieu` found no matching theorem. Laurent polynomials and additive monoid algebras exist.
- Algebraic `Mathlib/Algebra/Lie/Sl2.lean`, weights, root systems, and `Geometry/Manifold/GroupLieAlgebra.lean` exist. No highest-weight existence theorem or root-subgroup integration theorem was located in the initial search. This is an investigation item, not yet an exception.
- Continuous representations and Haar uniqueness/pushforward infrastructure exist. Exact declarations reused will be recorded below.

## Imported results actually used

- `Measure.haarMeasure`, `Measure.haarMeasure_self`, `MonoidHom.measurePreserving`, `integral_map_of_stronglyMeasurable`: normalized Haar construction and pullback, no extra countability hypotheses.
- `IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_ne_zero_of_eq_nat` and `.pow_toEnd_f_eq_zero_of_eq_nat`: lowering identities in an existing finite-dimensional module. These do not supply L02/L06.
- `Polynomial.derivative_monomial`, `derivative_comp`, `coeff_derivative`, `X_pow_dvd_iff`: primitive congruence.
- `Polynomial.coeff_one_add_X_pow`, `coeff_X_pow_mul'`, `Nat.choose_symm`, `Nat.choose_pos`: Pascal coefficients and ranges.
- `Polynomial.hasDerivAt`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, continuity implies interval integrability: the moment recurrence and primitive/integral correspondence.
- `AddMonoidAlgebra.support_coeff_mul_subset`, `Set.Finite.isCompact_convexHull`, `geometric_hahn_banach_point_closed`, `exists_nat_gt`: separating-functional proof, retaining cancellation in support containment.
- `LaurentPolynomial.T_add`, `T_pow`, `single_eq_C_mul_T`: exact transformed Laurent expansion and spectrum.

## Validation and correspondence audit

Current full library build passed (3625 jobs). The verifier moved unchanged to `scripts/verify_mathieu_classification.py`; its output exactly matches `scripts/verify_mathieu_classification.txt` (diff exit 0). H09 now has the complete primitive and integral/substitution correspondence proved; L05 has both lowering identities but full submodule equivalence is pending. Lemma `lem:haar-pullback` is now fully proved, including actual representative-function witness transport. Final classification and uniform theorem axiom audits are not available because those theorems have not been proved.

## Resume notes

Read the current Lean files and the current state above. Never infer that an intended theorem name exists merely because it occurs in the ledger. Do not remove outstanding obligations or replace them with conditional surrogates.


## Detailed obstruction investigation (2026-09-17 UTC)

### Torus noncancellation, independent of the group-theory layer

The minimal current target is already the two-variable case:

```lean
∀ f : MultiLaurent 2, f ≠ 0 →
  (0 : Fin 2 → ℝ) ∈ newtonPolytope f →
  ∃ m : ℕ, 1 ≤ m ∧ constantTerm (f ^ m) ≠ 0
```

`MultiLaurent`, `constantTerm`, and `newtonPolytope` are actual definitions in
`MathieuProperty/LaurentSupport.lean`. `scripts/CheckObligations.lean` checks the
syntax/types of this target and the full manuscript target; it supplies NO proof.
The full target is manuscript `thm:dvdk`; `cor:torus` and `thm:classification`
depend on it. No version of that implication is used as a hypothesis in the current
library. The strongest currently proved downstream statement is
`eventual_constantTerm_zero_of_newton`: once zero is outside the actual Newton
convex hull, every fixed multiplier has eventually zero constant term.

Attempts and their exact limits:

1. Whole-source searches of pinned mathlib for Duistermaat, van der Kallen, Mathieu,
   Newton polytope and constant-term formulations found no such theorem. Inspected
   Laurent polynomials, additive monoid algebras, support products, convex hulls,
   and separation. These APIs suffice to prove the separation-to-eventual-vanishing
   half, now implemented.
2. Direct coefficient/support proof: proved monomial-power coefficients and support
   bounds. Positive integer combinations of exponents only show that zero CAN
   occur; they do not show that its complex coefficient survives cancellation.
   `MathieuProperty.cancellationExample_square` checks CT(f²)=0 for
   f=x+x⁻¹+i(y+y⁻¹), ruling out the naive positive-count argument. No implication
   from a vanishing single moment to support separation is claimed.
3. Alternative univariate encoding: integer specialization x_i↦t^{a_i} changes the
   constant term by merging distinct exponent vectors. A map ℤ²→ℤ has a nontrivial
   kernel, so injectivity on the original finite support cannot ensure injectivity
   on supports of all unbounded powers. Thus applying a one-variable theorem to a
   specialization does not provide the needed conclusion.
4. Alternative finite group algebra/trace argument: reduction modulo a large lattice
   preserves only a bounded range of powers; sufficiently high powers wrap around
   and contribute new constant terms. Nilpotence results in finite group algebras
   consequently do not prove the Laurent statement for all positive powers.
5. Read the original proof in Duistermaat–van der Kallen (1998), Theorems 4–5.
   Its arbitrary-rank route uses toroidal compactification, resolution of
   singularities, and analytic continuation/asymptotics of period integrals.
   Searched the pinned library for those infrastructures (including Hironaka,
   toric varieties, Gauss–Manin, Nilsson and residue formulations), with no usable
   implementations found. This is not a missing coefficient simplification lemma.
6. Investigated the alternative algebraic/Puiseux proof in van den Essen–Schoone
   (2025); its stated scope is dimension one and does not remove the rank-two
   obstruction. No Newton–Puiseux theorem was found in pinned mathlib either.
7. Checked the relevant older local gamma-torus Lean project. Its `ProofInputs`
   structure assumes the exposed-face step where this theorem enters; it is not
   an unconditional theorem that can be reused under the present soundness rules.

Primary sources consulted:
- [Duistermaat–van der Kallen original paper](https://wilberdk.home.xs4all.nl/publications/powers.pdf).
- [van den Essen–Schoone, dimension-one generalization](https://doi.org/10.1016/j.jpaa.2024.107847).
- [Zhao–Willems, finite group-algebra analogue](https://arxiv.org/abs/1009.5794).

### Compact-group root existence, independent of the torus layer

The algebraic finite-dimensional highest-weight-one lowering step was implemented
using `Mathlib/Algebra/Lie/Sl2.lean`. This is a direct specialized proof of the
specific lowering assertions, not an assumption of the doublet lemma.
It requires an existing sl₂ triple and primitive weight-one vector. Those data
are not constructed from an arbitrary compact simply connected simple group.

The original route needs existence of the fundamental group representation and
integration of a root Lie algebra. Searched all weights/root-system/Serre/sl₂
files and the manifold/group files. `GroupLieAlgebra` has uses only in its own
file and the alternative invariant-derivation construction; no compact Lie
algebra decomposition, differential homomorphism integration, compact
highest-weight representation existence, or root subgroup theorem was located.

Alternative route considered: realize G faithfully as a unitary matrix group and
construct the subgroup there. The matrix and algebraic representation APIs exist,
but this route still requires faithful finite-dimensional continuous compact-group
representations and a group/Lie-algebra bridge. No Peter–Weyl implementation was
located. Changing the matrix model does not produce these existence theorems.
A minimal necessary fragment, a continuous injective SU(2) homomorphism under the
standard compact, connected, simply connected, simple Lie-algebra hypotheses, is
recorded as an unproved type-checked target in `scripts/CheckObligations.lean`.
It is strictly less than the full `lem:root-doublet`, so proving just that fragment
would still not complete the paper.

### Model and correspondence cautions for continuation

- `Hopf.Space = ℂ × ℂ` uses its product topology. The sphere is explicitly
  `{z // a z = 1}`. The product's default sup norm is NOT the Euclidean radial
  norm. The checked `Hopf.sphereHomeomorph` now identifies it with the sphere
  in `WithLp 2 (ℂ × ℂ)`, and `norm_sq_eq_a` proves the norm correspondence.
  Do not substitute the default product norm in later radial proofs.
- `haarIntegral` is on continuous functions; `representativeIntegral` is its proved
  linear restriction to the finite-span representative algebra. `HasMathieuProperty`
  uses the kernel of this actual functional, with no surrogate closure assumptions.
- Formal spectrum is over the polynomial coefficient ring; it is not the spectrum
  after fixing x at an endpoint where some coefficients vanish.
- The root target uses the actual manifold Lie algebra and conventional structural
  hypotheses, not a custom class containing the desired root embedding.
- A successful build and axiom audit certify the current proofs only. They say
  nothing about missing ledger obligations or the unproved main theorems.

## Milestone validation commands

```sh
lake build
python3 scripts/audit_sources.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/CheckObligations.lean
python3 scripts/verify_mathieu_classification.py > /tmp/mathieu-verification.txt
diff -u scripts/verify_mathieu_classification.txt /tmp/mathieu-verification.txt
```

The checked-in `scripts/axiom-audit.txt` records the current dependency audit.
The main classification and uniform marker-tower theorems have no axiom reports
because no declarations proving them exist yet. Foundational axiom whitelist:
`propext`, `Classical.choice`, `Quot.sound`. All auxiliary tools and outputs stay
under `scripts/`; normal mathematical modules stay under `MathieuProperty/`.


Current inventory counts: PROVED=54, TODO=46, IN PROGRESS=4, BLOCKED=6 (110 rows).

## Foundation milestone audit (not the final whole-paper audit)

- Rebuilt all project modules after removing build products and restoring only the pinned dependency cache: `lake build` passed (3533 jobs).
- 10 mathematical modules and one umbrella; 55 explicit theorem/lemma declarations.
- 105 ledger rows: 24 PROVED, 66 TODO, 9 IN PROGRESS, 6 BLOCKED.
- All 18 named results plus the named definition have ledger entries. Named results remain incomplete; the named definition is implemented.
- `scripts/CheckObligations.lean` type-checks both torus targets and the root-embedding target, without claiming to prove them.
- Source audit passes and checks that every mathematical module is reachable from the build umbrella.
- Whole-namespace transitive axiom audit passes; see `scripts/axiom-audit.txt`.
- Verifier and its checked-in output are byte-identical to the original files; fresh output matches exactly.
- Manuscript diff is empty.
- Proof substitutions: formal coefficient divisibility replaces the prose polynomial congruence calculation; an elementary derivative/integration recurrence proves c_m's factorial formula without relying on the beta function. Neither substitutes for the sphere-measure theorem.
- No classification theorem, uniform marker-tower theorem, or conditional surrogate thereof was added. The final adversarial whole-paper audit cannot pass while outstanding obligations remain.

## Repository review record

Foundation proof commit: `6bec9eee6121ba45890baa3328dd9128fcecf974`.
[PR #1](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/1)
contains the foundation milestone and the verifier relocation. It is explicitly
labelled partial coverage; its build result must not be read as full-paper certification.
The PR description records the source, transitive-axiom, correspondence and
symbolic-verifier self-review. Merge only after the PR checks succeed.

## Representative-function milestone (M1)

`RepresentativeFunctions.lean` implements continuous complex matrix representations,
finite coefficient spans, and the unital star algebra. This is a coordinate model
of the manuscript definition, with explicit correspondence proofs:

- `representation_coefficient_mem` maps coefficients from arbitrary finite-dimensional
  normed complex representation spaces (in any universe) into this algebra using a basis.
- `representative_eq_span_coefficients` and `representative_algebra` identify the
  constructed algebra exactly with finite linear combinations of ordinary coefficients.
- `continuous_action` proves joint continuity. This matters because mathlib's
  `ContRepresentation` alone asserts continuity of individual linear operators,
  without requiring continuity in the group variable.
- `tensor_toMatrix` identifies Kronecker matrices with `Representation.tprod` in
  the tensor basis. `coefficient_mul` proves the full arbitrary-vector/covector formula.
- `conjugate_action` and `coefficient_conj` prove the conjugate representation assertions.
- `representativePullback` is an actual algebra homomorphism on these algebras.

`Haar.lean` now proves integrability, defines the normalized linear functional on
representative functions and `HasMathieuProperty`, and proves the full quotient
pullback and failure statements. No compact-group classification, root-subgroup,
or Laurent noncancellation theorem is assumed in these declarations.

The manuscript is unchanged. The remaining library obstructions are unchanged,
but they do not prevent completing these independent obligations.

M1 validation: `lake build` passed (3539 jobs); source audit passed for 14 Lean files; transitive axiom audit passed for 246 project declarations (177 theorem constants, including generated declarations). The whitelist remains `propext`, `Classical.choice`, `Quot.sound`. Outstanding statement checks pass.

## Hopf integral-kernel milestone (partial M3)

M1 was merged as [PR #2](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/2)
at main commit `bc7912192c8dc8a12671bd9ea2e0dafafee0d8a8` after successful CI.

`HopfIntegralKernel.lean` now proves the analytic coefficient kernel on `[0,1]`:
the integral of coefficient m of
`H(X)(1+X)^m(1-(1+X)^2 t^2)^m` equals
`c_m * coeff m (H(X)(1+X)^(m-1))` for all positive m and all complex polynomials H.
Finite binomial sums justify integrability and interchange; complex FTC proves
substitution without dividing by `1+X`. This covers the zero-parameter case too.

`PhaseAverage.lean` proves normalized phase extraction for arbitrary Laurent
polynomials with all integer exponents, and identifies its finite-sum expression
with mathlib's actual Laurent evaluation at every nonzero complex radius.
`MomentConstant.lean` now includes the beta and double-factorial forms as well as
the already-proved factorial form and positivity.

These proofs do NOT identify the coordinate integral with normalized surface
measure on S³. H05 and the corresponding part of H08 remain open; consequently
`thm:hopf-coefficient` and `cor:sphere-marker-tower` remain unproved.

Further library search found `Measure.toSphere` and
`measurePreserving_homeomorphUnitSphereProd` in `HaarToSphere.lean`, plus
`WithLp 2 (ℂ × ℂ)` with the Euclidean product norm and compatible volume in
`Haar/InnerProductSpace.lean`. These are potential starting points for the
remaining measure correspondence, not already-proved Hopf-coordinate formulas.

Integral-kernel validation: `lake build` passed (3605 jobs); source audit passed for 16 Lean files; transitive axiom audit passed for 281 project declarations (210 theorem constants, including generated declarations). There are 103 explicit theorem/lemma declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Outstanding target statements still type-check.

Additional library dependencies: `TensorProduct.toMatrix_map`, `LinearMap.toMatrixAlgEquiv`, `Module.finBasis`, and `Submodule.span_induction` establish the representative-coordinate correspondence; `Complex.betaIntegral_eval_nat_add_one_right` and `Nat.doubleFactorial_add_two` establish the remaining moment-constant forms; `HasDerivAt.comp_ofReal`, complex FTC, `intervalIntegral.integral_finsetSum`, and `integral_exp_mul_complex` establish the new analytic steps.

## Sphere measure and radial preliminaries (partial M3/M4)

The integral-kernel milestone was merged as
[PR #3](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/3)
at `d2ba09f226a1cf7b7d1f99a6e103329c9571f30e` after successful CI.

`SphereMeasure.lean` supplies the canonical Euclidean sphere model and normalized
surface probability measure, transported through a proved homeomorphism to the
manuscript's `a(z)=1` sphere. `norm_sq_eq_a` explicitly distinguishes the Euclidean
norm from the ambient product sup norm. Compactness and all polynomial-moment
integrability are proved.

The cone defining `Measure.toSphere` above `u=0` lies in the two ambient coordinate
planes, which have Lebesgue measure zero. This proves `surfaceMeasure_u_zero` and
the actual almost-everywhere rational formula `p_localization_ae`; no Hopf-coordinate
density is assumed to establish either fact.

For finite Borel measures on ℂ² with compact support, continuous integrands and
all polynomial Hopf moments are integrable. The radial scaling law includes zero
scalars; the exponent is exactly `4m+s` (equivalently `8m+2s` in the radius).
`radial_integral_pos` proves strict positivity of every positive radial moment
from positive mass off the origin.

Remaining immediate work: prove the exact Hopf-coordinate measure formula or a
fully justified alternative computation of these actual surface moments. The
surface measure has been defined from mathlib's Euclidean cone construction;
its coordinate density and the SU(2) orbit/Haar correspondence are still open.
The separate root-group and Laurent noncancellation obstructions remain unchanged.

Sphere/radial validation: `lake build` passed (3610 jobs); source audit passed for 17 Lean files. The whole-namespace axiom audit passed for 354 declarations (275 theorem constants, including generated declarations), with only the three approved foundations. There are 125 explicit theorem/lemma declarations in 14 mathematical modules. Outstanding target statements still type-check.

## Coordinates, surface symmetry, and orbit averaging

The surface/radial milestone was merged as
[PR #4](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/4)
at `a3ce0b5bd97c39b8405ecd7bd5ef266234b24e09` after successful CI.

`HopfCoordinates.lean` defines the actual square-root/exponential parametrization,
proves its a, τ, and u formulas, continuity, and surjectivity onto the sphere.
The u-coordinate is nonzero in the open t-interval. Surjectivity uses unrestricted
real angles; no restricted-angle density formula is claimed yet.

`SphereSymmetry.lean` proves that every real linear isometry of the Euclidean
ambient space preserves the constructed normalized surface measure. The proof
commutes the isometry with the cones defining surface measure and uses its actual
Lebesgue measure preservation. Invariance is proved rather than built into a
custom measure specification.

`OrbitAverage.lean` proves the action map sends probability Haar × μ to μ for an
invariant finite measure, then derives product integrability and Fubini's identity
for every μ-integrable complex function. It also separately proves product
integrability for continuous functions with compact measure support. These are
general continuous-action results; constructing and connecting the defining SU(2)
action is part of the outstanding R01/R02 obligations.

Continuation priorities:
1. Construct the defining SU(2) action and its explicit transitive sphere matrices,
   connecting their norm preservation to `surfaceMeasure_preserving`.
2. Identify Haar orbit measure with surface measure using transitivity and averaging.
3. Prove the exact coordinate density or a fully justified surface-moment substitute.
   `Complex.integral_comp_pi_polarCoord_symm` in `Analysis/SpecialFunctions/PolarCoord`
   and `Measure.measurePreserving_homeomorphUnitSphereProd` are available for the
   coordinate route. An alternative is to derive coordinate polynomial moments
   from orthogonal invariance; this remains a plan, not a proved result.
4. Combine the actual sphere moments with the proved integral kernel, phase extraction,
   integrability, and orbit averaging to complete M3/M4.

No central theorem is added under assumptions of these remaining correspondences.

Coordinate/symmetry validation: `lake build` passed (3613 jobs), the source audit passed for 20 Lean files, and the namespace axiom audit passed for 388 declarations (305 theorem constants including generated declarations). There are 142 explicit theorem/lemma declarations in 17 mathematical modules. Only `propext`, `Classical.choice`, and `Quot.sound` occur; outstanding target statements still type-check.


## Defining SU(2) action and radial reduction

The coordinate/averaging milestone was merged as
[PR #5](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/5)
at `077903cac290bf764dde5dc03919e9788a01513b` after successful CI.

`SU2Action.lean` uses mathlib's actual `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
The explicit first-column matrix defines a homeomorphism with the unit sphere;
its inverse is derived from the unitary and determinant-one equations, using the
adjugate identity. This proves compactness. The defining continuous linear action
on ℂ² preserves `a`, gives a real Euclidean linear isometry, and preserves the
previously constructed surface measure. Explicit matrices prove transitivity.
`SU2Orbit.lean` extends transitivity to every level of `a`, including zero.

`Haar.lean` now proves right invariance of normalized Haar measure on any compact
group using Haar uniqueness and total mass one. `OrbitMeasure.lean` proves that a
transitive continuous action of a compact group sends normalized Haar to its
invariant probability measure. Its proof uses Tonelli and the proved right
invariance; transitivity and invariance are discharged explicitly for SU(2).
Consequently `su2_orbit_map` identifies Haar orbit measure with the actual
normalized Euclidean surface measure, not a newly stipulated measure.

`su2_orbit_moment` proves for every z and all natural m,s that the orbit moment is
`a(z)^(4m+s)` times the corresponding sphere moment. The proof includes zero.
`radial_moment_factorization` integrates this identity for any finite compactly
supported SU(2)-invariant Borel measure. It uses the already proved orbit averaging
and integrability results. No sphere coefficient identity is assumed in these
statements. R01 and R02 are now fully proved; the named radial-transfer theorem
still depends on the unproved sphere coefficient formula.

Next work: establish the sphere polynomial moments, then combine them with the
proved coefficient kernel and radial factorization. The coordinate Jacobian route
remains available. A possible alternative is to derive mixed coordinate moments
from unitary invariance by polynomial coefficient comparison, then prove the
surface integration formula on polynomial functions. This alternative has not
been proved yet and does not close H05 (the exact coordinate-density statement).
The independent root-group and Laurent noncancellation obstructions are unchanged.

SU(2)/orbit validation: `lake build` passed (3616 jobs); source audit passed for
23 Lean files; whole-namespace axiom audit passed for 449 declarations (356 theorem
constants, including generated declarations), using only the three approved
foundations. There are 165 explicit theorem/lemma declarations in 20 mathematical
modules. All 105 ledger obligations remain inventoried: 42 proved, 51 TODO,
6 in progress, 6 blocked. The symbolic verifier reproduces its checked-in output
exactly; precise outstanding-obligation statements still type-check.


## Full Hopf coefficient and radial-transfer milestone

The SU(2) action/orbit milestone was merged as
[PR #6](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/6)
at `656fc8d51bb24fee7ab63e3226a6d37264c62331`, with successful CI.

The named Hopf coefficient theorem, sphere marker tower, and universal radial
transfer are now proved. The five new ledger obligations H15–H19 explicitly record
the load-bearing steps of the replacement sphere-moment proof. Every original
obligation remains listed; the ledger now has 110 entries.

Material proof substitution for the Hopf coordinate Jacobian:
1. Diagonal SU(2) phases force every coordinate monomial of nonzero phase weight
   to have zero sphere integral.
2. Apply this to a homogeneous monomial after the unnormalized matrix with first
   column (1,t). The coefficient of t gives
   `(q+1) M(p+1,q) = (p+1) M(p,q+1)`. The identity a=1 gives
   `M(p,q) = M(p+1,q) + M(p,q+1)`.
3. These recurrences and probability normalization prove
   `M(p,q) = p! q! / (p+q+1)!`. Polynomial induction proves the first squared
   coordinate's uniform polynomial marginal, hence τ's uniform polynomial marginal.
4. A continuous SU(2) phase action sends u to u exp(iθ) while fixing τ. Compact
   integrability proves the required Fubini identity. Localization is used only
   off the already proved null endpoint circles. Finite phase sums extract the
   exact coefficient of the manuscript's kernel.
5. The τ marginal and evenness give the manuscript's integral over [0,1]. The
   existing primitive coefficient theorem finishes `Hopf.hopf_coefficient`.

All positivity statements for complex moments are expressed as equality to a
strictly positive real number. `sphere_marker_tower` contains the pure formula,
all marked formulas, the s>m zero range, and the 1≤s≤m positive range.
`radial_transfer` additionally contains nonconcentration and strict positivity of
the real radial integral, for every finite compactly supported invariant Borel
measure on ℂ². It uses the actual defining action and the already proved orbit
factorization. No sphere formula is supplied as a hypothesis.

H05 remains IN PROGRESS: its normalized Euclidean measure, coordinate map,
endpoint nullity, and coordinate formulas are proved, but the full three-variable
coordinate-density identity is not yet proved. The replacement proof establishes
all integrals needed for the named Hopf/radial results without asserting that
remaining density claim. The root-group and Laurent noncancellation blockers
remain unchanged. Next work can address H05, explicit SU(2) representative
witnesses, or the remaining representation and descent steps.

Hopf/radial validation: `lake build` passed (3624 jobs); source audit passed for
31 Lean files; whole-namespace axiom audit passed for 584 declarations (479 theorem
constants, including generated declarations), using only `propext`,
`Classical.choice`, and `Quot.sound`. The audit explicitly prints these dependencies
for `hopf_coefficient`, `sphere_marker_tower`, and `radial_transfer`. There are
221 explicit theorem/lemma declarations in 28 mathematical modules. The symbolic
verifier reproduces its checked-in output exactly; precise outstanding-obligation
statements still type-check. The manuscript is unchanged from its initial commit.
This is a milestone correspondence check, not the final full-paper audit.


## Actual SU(2) representative-function witness

The full Hopf/radial milestone was merged as
[PR #7](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/7)
at `d2249e11129fa3f2798bf3502f5a5c1507c3935d`, after CI run `35176531343`
succeeded, including the complete build, source and axiom audits, and verifier.

`SU2Witness.lean` proves all four matrix-entry representatives A₀,U₀,V₀,T₀ and
identifies their polynomial pair with the Hopf pair on the first column. The
actual defining matrix representation supplies four elements of the finite
representative algebra. Evaluating the entry polynomials there constructs
`su2P` and `su2Q`, with no assumed representative-function membership.
The Haar/sphere correspondence proves every positive pure moment is zero and
all marked moments have the Pascal formula for these actual algebra elements.
`Hopf.SU2_not_mathieu` refutes the manuscript's Mathieu property for SU(2), with
fixed witness `su2P` and multiplier `su2Q`. This is the SU(2) special case only;
the general nonabelian classification and uniform theorem remain unproved.

This completes E06. The remaining explicit transformed-witness work includes
E05 (the weighted x-integral/constant-term formula), and E09/E14 (the external
transform correspondence). All original and replacement-proof obligations
remain tracked. Auxiliary tools and outputs remain under `scripts/`.

SU(2) witness validation: `lake build` passed (3625 jobs); source audit passed for
32 Lean files. Whole-namespace audit passed for 612 declarations (502 theorem
constants), with only the three approved foundations, including `SU2_not_mathieu`.
There are 231 explicit theorem/lemma declarations in 29 mathematical modules.
The ledger has 54/110 obligations proved. The verifier output matches exactly,
and the precise outstanding statements still type-check.


## Explicit weighted Laurent moments

The SU(2) representative witness was merged as [PR #8](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/8)
at `c9dda6f2ce9a52a2111c1e8d74b8a5798194ad49` after CI run `35176945277` passed.

`AbelianConstantTerm.lean` specializes the actual coefficient polynomials of
`formalP` and `formalQ`. Coefficient extraction after the substitution X=cw
and the defect-one identity prove the constant-term formula at every real
0<x<1. Nonzero c=2x(1-x²) is proved in that interval; no division is performed
at either endpoint. Polynomial continuity provides all needed integrability.

`AbelianWitness.lean` defines the exact functional
`weightedCT f = 2 * ∫ x in 0..1, (f.coeff 0).eval x * x`.
A checked change of variables t=1-2x², its derivative -4x, and evenness give
the manuscript's normalization. Equality off the endpoints suffices by their
Lebesgue nullity. The existing Hopf coefficient theorem proves all pure and
marked weighted moments. `explicit_laurent_witness` packages the pure formula,
all positive marker formulas, and the exact formal spectrum. Additional theorems
state the zero and strictly positive marker ranges.

This completes E05. The proposition remains IN PROGRESS because E09/E14,
its identification with the external Müger–Tuset group-coordinate transform,
is not yet proved. No external reduction theorem is assumed.

Weighted-witness validation: `lake build` passed (3627 jobs); source audit passed
for 34 Lean files. Whole-namespace audit passed for 645 declarations (532 theorem
constants), with only `propext`, `Classical.choice`, and `Quot.sound`.
There are 247 explicit theorem/lemma declarations in 31 mathematical modules.
The ledger has 55/110 obligations proved. The verifier output matches exactly,
the outstanding statements still type-check, and the manuscript remains unchanged.
