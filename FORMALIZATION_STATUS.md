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

- Development branch: `formalization/cartan-root-compatibility`; milestones through [PR #53](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/53) are merged. Use `git status` for the live checkout after merging.
- Lean: `leanprover/lean4:v4.34.0`.
- mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0).
- M0 and M1 complete; the library covers 166 mathematical modules plus the import umbrella. The Hopf coefficient theorem, sphere marker tower, and universal radial-transfer theorem are proved, as are the representative-algebra and Haar-pullback lemmas. The main classification, uniform nonabelian tower, root subgroup existence, and torus direction remain outstanding. The exact Hopf coordinate-density obligation H05 is now proved as well; the original sphere theorem retains its documented invariant-moment proof.
- Milestones through the fractional 2024 G2 counterexample are merged and CI-checked ([PR #31](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/31)). The general classification remains unproved; ordinary obligations continue alongside investigation of the foundational gaps. No weakening or conditional main theorem is authorized.
- No manuscript mathematical error has been identified. The detailed investigation below records missing Duistermaat–van der Kallen and representation/root-integration infrastructure. These remain formalization gaps; no cited result is assumed, and the audited manuscript is unchanged.

## Work allocation following user clarification (2026-09-17)

The user has directed that general multivariate Duistermaat–van der Kallen
remain a documented blocker, pending their external work on a resolution-free
proof. Do not continue attempting the existing resolution-dependent proof or
build Hironaka infrastructure for this project. Resume this obligation only
when a concrete new proof or usable formal infrastructure becomes available.
This is a limitation of the currently available proof route and library, not a
claim that Lean cannot express or ultimately prove the theorem.

The checked one-variable theorem and circle Mathieu property remain complete.
T04 retains IN PROGRESS to record that partial coverage; its arbitrary-rank
portion is deferred. The general torus theorem and classification remain
BLOCKED and must not be asserted conditionally as completed results. Continue
independent attainable obligations. The adjoint simple quotient and the
compact abelian torus identification are now proved. Record additional foundational blockers explicitly rather than
repeatedly pursuing unavailable proof routes.

## Remaining work: dependency-aware assessment

The five BLOCKED rows do not mean that all other rows can be completed
independently. Counts describe coverage, not an estimate of remaining effort.
In particular, IN PROGRESS can include completed transfer lemmas whose general
existence inputs are blocked.

| Remaining obligation | Current allocation / dependency |
|---|---|
| G04 and adjoint simple quotient | Now proved: actual open image, inherited Lie algebra, identity component, and continuous quotient map. |
| General DvK (unproved part of T04), general torus theorem, classification | Deferred pending the external resolution-free DvK route. Classification also depends on the nonabelian direction. |
| L02 fundamental highest-weight representation; L06 root integration | Foundational gaps already documented; no existence assumptions added. |
| L04 weight-one root restriction | Now proved from the standing algebraic Cartan, root-base, and highest-weight-vector data; the root triple is constructed, not assumed. |
| Root-doublet lemma and general simply-connected-simple theorem | Depend on the highest-weight/root-integration gaps; checked algebraic restriction and transfer proofs do not construct the required group representation. |
| Simple central forms and uniform nonabelian theorem | Depend on the general simple-group result and Z05; the adjoint quotient needed by the uniform theorem is now proved. |
| L01 root/weight setup | Now proved: an actual maximal torus, its smooth injective inclusion with differential image equal to the real Cartan, the scalar-extension splitting Cartan, simple roots, and a fundamental weight with coroot pairing one. Highest-weight representation existence and root integration remain separate gaps. |
| Z05 simple cover | Finite center, covering onto the center quotient, centrality of covering kernels, and topological quotient identification are proved. Existence and compactness of the simply connected cover remain open; the finite-fundamental-group fragment is only type-checked. |
| T01 abelian iff torus | Now proved via actual one-parameter subgroups and a full kernel lattice; independent of DvK. |
| E13, E14 and remaining external abelian reductions | Exact SO source correspondence is unresolved because of the documented external indexing discrepancy; other specified counterexamples are already checked. |

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
| lem:root-doublet | Fundamental highest-weight representation contains a faithful defining SU(2) root doublet | sl2Doublet_cyclic; sl2Doublet_matrix; root_hom_injective | RootDoubletModule / RootDoubletFaithfulness / RootSU2 (planned) | L01–L07 | IN PROGRESS | Manuscript | The cyclic irreducible algebraic doublet, defining matrices, and faithfulness of a supplied defining action are checked. Fundamental representation and root integration are absent. |
| lem:radial-pushforward | Projected Haar is compactly supported invariant probability, not concentrated at zero | doublet_radial_pushforward | ProjectedHaar | lem:root-doublet; L08–L11 | PROVED | Manuscript | Given the manuscript’s standing unitary doublet data: actual projected Haar probability, compact ball support, SU(2) invariance, and positive mass off zero. Root-doublet existence remains open. |
| thm:simply-connected-simple | Representative A,P,Q, nonnegative nonzero A, exact tower on all compact simply connected simple groups | doublet_pure; doublet_marked; doublet_marked_positive; unitary_doublet_not_mathieu (transfer only) | DoubletWitness / RootSU2 (planned) | lem:radial-pushforward; thm:radial-transfer; lem:representative-algebra | IN PROGRESS | Manuscript | Complete representative-function transfer proved for explicitly supplied unitary defining-doublet data. Existence of those data for all simply connected simple groups is unproved; no general simple-group theorem claimed. |
| prop:classical-closed-forms | Defining SU(n), n≥2, and Sp(n), n≥1: rising factorial formulas and printed examples | specialUnitary_closed_forms; compactSymplectic_closed_forms; specialUnitary_small_values; compactSymplectic_small_values | ClassicalSU / ClassicalSp / SphereBeta / SymplecticOrbit | C01–C07; projected_haar_moments | PROVED | Explicit matrix-root action and radial transfer | Both families are proved for all stated ranks with actual representative functions, pointwise first-column Hopf identities, normalized Haar moments, endpoints, and printed examples. Uses explicit SU(2) blocks, so no general root-existence theorem is assumed. |
| lem:center-descent | Six functions descend as representative functions through full center and intermediate quotients | doublet_center_invariant; center_descent | CenterDescent | Z01–Z04; H04 | PROVED | Manuscript | For the standing irreducible unitary representation and projected coordinates: all six functions are invariant under the full center and descend as actual representative functions through every central subgroup. No universal representation-existence claim. |
| cor:simple-central-forms | Exact marker tower and Mathieu failure for every compact connected simple central form | center_quotient_tower (transfer only) | QuotientWitness / SimpleGroups (planned) | Z05; lem:center-descent; lem:haar-pullback; thm:simply-connected-simple | IN PROGRESS | Manuscript | All moments, nonnegative nonzero A, strict positivity, and Mathieu failure descend through every central quotient of a supplied irreducible defining doublet. Universal source representation and simple-cover existence remain unproved. |
| prop:adjoint-simple-quotient | Every nonabelian compact connected Lie group surjects continuously onto adjoint compact simple group | CompactAdjoint.adjoint_simple_quotient | AdjointQuotient | G01–G06 | PROVED | Manuscript, with local openness replacing the closed-subgroup step | Actual compact connected centerless Lie-group target, simple group Lie algebra, continuous surjection, and identification with the automorphism identity component of a simple ideal. |
| thm:uniform-nonabelian | Full manuscript quantifiers, representative triple and radial moment tower, positivity and vanishing | uniform_nonabelian | MainTheorem | prop:adjoint-simple-quotient; cor:simple-central-forms; lem:haar-pullback | TODO | Manuscript |  |
| thm:dvdk | Nonzero complex multivariate Laurent f with all positive-power constant terms zero has Newton polytope avoiding zero | duistermaat_van_der_kallen | Torus | T04 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| cor:torus | Every torus has the Mathieu property | torus_mathieu | Torus | T01–T08; thm:dvdk | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| thm:classification | For every compact connected Lie group: Mathieu property iff abelian iff torus | classification | MainTheorem | thm:uniform-nonabelian; cor:torus; T01 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| prop:explicit-abelian-SU2 | Transformed Laurent pair: exact moments, printed expansion, exact spectrum | Abelian.formal_expansion; Abelian.formal_spectrum; Abelian.transform_correspondence | AbelianAlgebra / AbelianLaurent / TransformPair | E01–E09; thm:hopf-coefficient | PROVED | Manuscript; specialized moment comparison and polynomial interpolation for the external correspondence | Algebra, spectrum, weighted moments, formal representative independence, and actual Haar correspondence checked. |
| cor:abelian-reductions | Failure of both universal abelian conjectures, growth claim and specified Zwart reductions | Abelian.universal_moment_conjecture_false; Abelian.universal_convex_support_conjecture_false; Abelian.universal_growth_conjecture_false | AbelianConjectures | E10–E14; prop:explicit-abelian-SU2; thm:classification | IN PROGRESS | Direct witness | Both universal conjectures, the growth assertion, and all specified SU/Sp/G2 conjectures are refuted. Exact SO source correspondence remains open. |
| D-representative | Finite linear combinations of coefficients of finite-dimensional continuous complex representations | representativeFunctions; representative_eq_span_coefficients; representation_coefficient_mem | RepresentativeFunctions |  | PROVED | Coordinate model, with formal basis correspondence | Finite linear span, without topological closure; arbitrary finite-dimensional normed complex representation spaces and joint continuity checked. |
| D-haar | Normalized Haar integration on representative functions | normalizedHaar; representativeIntegral; representativeIntegral_one | Haar | D-representative | PROVED | Manuscript | Linear restriction to the representative algebra; integrability and normalization proved. |
| D-property | Mathieu property is Mathieu condition on the kernel of Haar integral | HasMathieuProperty | Haar | D-haar; def:mathieu-subspace | PROVED | Manuscript | Mathieu condition on the kernel of representativeIntegral. |
| D-hopf | a, τ, u, v, universal P,Q, sphere restrictions p,q | Hopf.a; Hopf.tau; Hopf.u; Hopf.v; Hopf.P; Hopf.Q; Hopf.Sphere; Hopf.p; Hopf.q | HopfAlgebra |  | PROVED | Manuscript |  |
| D-cm | Integral c_m and factorial/beta/double-factorial alternatives | momentConstant; momentConstant_factorial; momentConstant_beta; momentConstant_doubleFactorial | MomentConstant |  | PROVED | Substitute: integration recurrence and mathlib beta integral | All printed forms and positivity checked; beta equality uses the complex-valued Euler integral at positive real arguments. |
| D-CT | Coefficient and Laurent constant term conventions; negative coefficients zero | MultiLaurent; constantTerm; newtonPolytope | LaurentSupport |  | PROVED | Manuscript | AddMonoidAlgebra on Fin d → ℤ; coefficients include cancellation. |
| D-Phi | Orthogonal projection coordinates and group A,P,Q | projectionOrbit; doubletCoordinates; doubletA; doubletP; doubletQ | Projection / ProjectedRepresentatives | L08 | PROVED | Manuscript | Orthogonal projection, isometric coordinates, inner-product coordinate identities, and all six representative Hopf quantities constructed for explicit finite-dimensional unitary data. |
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
| H05 | Hopf-coordinate normalized surface measure, endpoints null | Hopf.hopfCoordinateMeasure_eq_surface; Hopf.hopf_coordinates_integral; Hopf.hopfCoordinates_surjective; Hopf.surfaceMeasure_u_zero | HopfCoordinateMeasure / SphereDetermination / SphereMeasure / HopfCoordinates | D-hopf; mixed sphere moments; beta and phase integrals | PROVED | Moment determination and affine change of variables | Unit-cube coordinate pushforward equals actual normalized Euclidean surface measure; exact manuscript density dτ dα dβ/(8π²) proved for continuous test functions, with full continuous-sphere unit-cube formula. Null endpoint circles and surjectivity were proved earlier. |
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
| L01 | Maximal torus, simple roots and fundamental weight with coroot pairing one | CompactRootSetup.maximal_torus_root_setup; CartanLift.exists_maximal_torus; ComplexParts.subalgebra_eq_baseChange; CompactCartanRootData.exists_root_triple | CompactRootSetup / CartanDifferential / ComplexCartan / CompatibleRootData | Actual group Lie algebra; Mathlib Cartan/base existence; constructed Cartan covering | PROVED | Cartan stabilizer and adjoint-cover construction; scalar-extension proof | The actual compact connected simple group contains the constructed maximal torus. Its inclusion is smooth and injective with injective differential whose image is precisely the real Cartan. The complex Cartan is the scalar extension of that same real Cartan; its simple-root base, fundamental weight with pairing one, and root triple are constructed. No highest-weight group representation or root SU(2) integration is claimed here. |
| L02 | Simply connected compact simple group admits irreducible representation of fundamental highest weight | fundamental_representation_exists | RootSU2 | L01 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| L03 | Average inner product to obtain invariant Hermitian metric | averagedInnerCore; unitaryModel_intertwines; unitaryModel_continuous; invariantInnerProduct_invariant; invariantInnerProduct_continuous | HaarUnitarization | D-haar | PROVED | Manuscript | Haar average is positive definite and invariant; arbitrary finite-dimensional complex normed representations have a continuous unitary model, continuously linearly equivalent to the original representation. |
| L04 | Root sl₂ action on highest vector has weight one | FundamentalRootWeight.root_highest_weight_one; FundamentalRootWeight.fundamental_lowering | FundamentalRootWeight | L01; L02 | PROVED | Manuscript | Fundamental weight is the dual simple-coroot coordinate. For the standing Cartan/root base and highest-weight vector, constructs the actual root triple and proves primitive weight one. Group representation existence and root integration remain L02/L06. |
| L05 | Highest-weight-one cyclic module: Fv≠0, F²v=0 and two-dimensional defining action | highest_weight_one_lowering; sl2Doublet_cyclic; sl2Doublet_finrank; sl2Doublet_irreducible; sl2Doublet_matrix | RootDoubletAlgebra / RootDoubletModule | L04 | PROVED | Manuscript | Actual cyclic Lie submodule, basis, dimension two, irreducibility, and exact defining matrices from a primitive weight-one vector. |
| L06 | Integrate compact root Lie algebra to SU(2) homomorphism and identify restricted representation | integrate_root_SU2 | RootSU2 | L04; L05 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| L07 | Faithfulness implies injective root map; orthonormal identification gives defining SU(2) action | root_hom_injective; specialUnitary_change_basis | RootDoubletFaithfulness | L06 | PROVED | Manuscript | Given the defining action supplied by L06: the root homomorphism is injective, and every unitary basis change preserves the full SU(2) matrix subgroup. Existence and integration remain unproved. |
| L08 | Invariant orthogonal complement and equivariant projection | invariant_orthogonal_complement; projection_commutes | Projection | L03; lem:root-doublet | PROVED | Manuscript | Standard unitary invariant-subspace lemma; no root existence assertion. |
| L09 | Phi continuous, equivariant, norm≤1, Phi(1)=e₀ | doubletCoordinates_continuous; doubletCoordinates_a_le; doubletCoordinates_one; doubletCoordinates_equivariant | Projection | L08 | PROVED | Manuscript | Coordinates constructed from an isometric defining doublet; a(Φg)≤1 is the squared Euclidean norm bound. Standing doublet data remain explicit. |
| L10 | Haar pushforward invariant probability supported in compact ball | doublet_radial_pushforward; haar_pushforward_ball_support | ProjectedHaar | L09; U-haar-map | PROVED | Manuscript | Pushforward of actual normalized Haar; support compact by continuous compact image and contained in the Euclidean unit ball. |
| L11 | Nonempty open sets have positive Haar; continuity gives nonconcentration | haar_pushforward_nonconcentration | ProjectedHaar | L09; D-haar | PROVED | Manuscript | Continuous preimage of the complement of zero is open and contains the identity; actual Haar positivity applies. |
| C01 | First column Haar on SU(n) is uniform complex unit sphere | specialUnitaryFirstColumn_map; specialUnitaryFirstColumn_apply | ClassicalOrbit / ClassicalTopology / ClassicalSphereGeometry / NormalizedSphere |  | PROVED | Manuscript | For n≥2, actual compact SU(n) acts continuously and transitively on the Euclidean unit sphere; normalized cone surface measure is invariant. Haar orbit pushforward equals this probability measure. |
| C02 | Complex Gaussian normalization produces sphere measure | gaussian_sphere; normalized_independent_complex_gaussian | GaussianSphere | C01 | PROVED | Manuscript, invariance proof | Normalization of independent real/imaginary Gaussian coordinates gives the actual normalized Euclidean sphere measure for n≥2, covering every use in the manuscript. The origin is a proved null set. |
| C03 | Squared coordinate norms are Dirichlet(1,…,1), first two sum Beta(2,n-2) | sphere_dirichletOne; sphere_two_coordinates_beta; specialUnitaryRadialA_map; specialUnitaryRadialA_moment | SphereBeta / GaussianRadii / GaussianSquare / GammaScale / FiniteGamma / GammaBeta | C02 | PROVED | Manuscript | Actual normalized sphere coordinate law identified with normalized independent unit-rate gamma construction of Dirichlet(1,…,1); positive-rate scaling is proved. First-two marginal is actual betaMeasure. Actual SU(n) radial Haar moments established for all n≥2. |
| C04 | Beta moments equal rising factorial ratios | beta_moment_ratio; beta_moment_integrable; beta_moment_product; beta_moment_nat; beta_two_moment | BetaMoments | C03 | PROVED | Manuscript | Actual mathlib betaMeasure: density shift, normalization, integrability, Gamma recurrence, and rising-factorial ratios for all positive integer parameters. |
| C05 | Sp(n) defining action transitive on complex 2n sphere with same invariant measure | exists_compactSymplectic_firstColumn; compactSymplecticSphere_transitive; compactSymplecticFirstColumn_map; compactSymplecticRadialA_moment | CompactSymplectic / SymplecticOrbit | C01; C03; C04 | PROVED | Specialized constructive proof | Closed unitary symplectic subgroup, exact determinant correspondence, paired SU(2) rotations and real orthogonal first-column construction. Actual normalized Haar maps to normalized Euclidean sphere measure; radial beta law and moments follow. |
| C06 | Endpoint n=2 for SU and n=1 for Sp: A=1 and ratio=1 | specialUnitaryRadialA_two; compactSymplecticRadialA_one; compactSymplecticRadialA_moment; su2CompactSymplecticOne | SphereBeta / CompactSymplectic / SymplecticOrbit | C01; C05 | PROVED | Manuscript | Both endpoint functions are identically one and all moments have the stated ratio; the actual Sp(1) subgroup is all SU(2), with a continuous multiplicative equivalence and continuous inverse. |
| C07 | Nine rational examples for m=1,2,3 | specialUnitary_small_values; compactSymplectic_small_values; classical_small_values | ClassicalSU / ClassicalSp / ClassicalConstants | C04; H12 | PROVED | Manuscript | Every displayed entry is an actual representative Haar moment for SU(2), SU(3), SU(4), and Sp(2). |
| Z01 | Schur lemma: center acts by scalar of modulus one | center_scalar; unitary_center_scalar | CenterDescent | L02; L03 | PROVED | Manuscript | mathlib algebraically closed Schur lemma; norm preservation gives scalar modulus one. |
| Z02 | Balanced coefficients invariant; tensor representation has trivial central action | doublet_center_invariant; MatrixRepresentation.balanced_tensor_trivial | CenterDescent | Z01; H04 | PROVED | Manuscript | All six phase-balanced quantities are invariant; the actual tensor/conjugate matrix representation is identity on every unit scalar action. |
| Z03 | Tensor conjugate representation factors continuously through central quotient | MatrixRepresentation.descend; MatrixRepresentation.balancedDescend; MatrixRepresentation.descend_coefficient | CenterDescent | Z02 | PROVED | Manuscript | Actual quotient homomorphism; quotient topology proves entry continuity and exact coefficient pullback. |
| Z04 | All six functions are coefficients of sums/tensor powers on quotient | MatrixRepresentation.descendedBalancedCoefficient_apply; MatrixRepresentation.descended_hopf_functions; center_descent | CenterDescent | Z03; lem:representative-algebra | PROVED | Manuscript | Quotient coefficients of the balanced tensor representation generate all six quantities inside the representative subalgebra. Final wrapper identifies them with orthogonal-projection coordinates. |
| Z05 | Any compact connected simple central form is central quotient of compact simply connected simple cover | SimpleGroupCenter.center_finite; SimpleGroupCenter.center_quotient_covering; CentralCovering.covering_kernel_central; CentralCovering.quotientEquiv | SimpleGroupCenter / CentralCovering / DiscreteFibers | Actual adjoint differential; local derivative estimates; Mathlib covering maps | IN PROGRESS | Standard local and topological arguments | Finite center and the actual covering onto the center quotient are proved for compact simple groups. Any existing connected covering homomorphism has central kernel and, when surjective, identifies its target with the topological quotient. Existence and compactness of the simply connected covering Lie group remain unproved. |
| G01 | Compact Lie algebra decomposes as center plus simple ideals | CompactAdjoint.compact_lie_decomposition | CompactLieStructure / LieLocalCoordinates / LieMixedDerivatives / InvariantLieDecomposition | Actual adjoint action; HaarRealForm; mathlib invariant forms and semisimple ideals | PROVED | Haar averaging and local mixed-derivative proof | Constructs the positive form, proves infinitesimal invariance, center complement, finite independent simple factors, ambient ideal embeddings, and inherited positive invariant forms. No structural hypothesis is assumed. |
| G02 | Connected nonabelian group has at least one simple ideal | CompactAdjoint.nonabelian_simple_ideal | ManifoldZeroDerivative / LieHomCalculus / ConnectedLie / NonabelianCompactLie | G01 | PROVED | Connectedness via zero differentials | Zero differential implies constancy; smooth homomorphisms are determined by their differential; abelian Lie algebra forces connected group abelian. Nonabelianity forces a simple factor, lifted to an actual ambient ideal. |
| G03 | Connected adjoint action preserves each simple ideal | CompactAdjoint.adjoint_preserves_simple_ideal; simpleAdjointRepresentation_continuous | LieIdealOrbit / AdjointIdeals | G01 | PROVED | Manuscript finite-permutation argument | Ad preserves the semisimple complement; its action on the finite atomic-ideal family is constant by connectedness and closed fibers. Each factor is an actual ambient ideal with continuous restricted representation. |
| G04 | Inner automorphism group is compact connected adjoint simple; automorphism identity component | CompactAdjoint.toSimpleAutomorphisms_range_eq_component; adjointSimpleGroup_algebraEquiv; adjointSimpleGroup_center_eq_bot | AdjointAutomorphism / OpenLieSubgroup / AdjointQuotient | G01 | PROVED | Concrete open adjoint image | The actual smooth restricted adjoint image is open and equals the automorphism identity component. Its inherited Lie-group structure has Lie algebra equivalent to the simple ideal; compactness, connectedness, and trivial group center are proved. |
| G05 | Restricted adjoint differential image equals ad(simple ideal) | CompactAdjoint.restrictedAdjoint_eq_simple; restrictedAdjoint_mfderiv; restricted_adjoint_differential_range | RestrictedAdjointAlgebra / ProjectedAdjoint / RestrictedAdjoint | G01; G03 | PROVED | Manuscript, expressed in the ambient endomorphism space | The canonical projection constructs a smooth map equal to the actual restricted representation. Its manifold differential is the restricted bracket, whose image is exactly ad of the ideal. The inner-automorphism Lie-group target itself remains G04. |
| G06 | Closed connected subgroup with full Lie algebra equals connected target | LieSurjective.surjective_of_surjective_mfderiv | LieSurjective | G04; G05 | PROVED | Substitute: local openness from surjective differential | A C¹ homomorphism with surjective differential at 1 is onto a connected target. Uses the Banach inverse-function/open-mapping theorem in charts and the open-subgroup argument; applies directly to the manuscript homomorphism once G04–G05 construct its target and differential. No closed-subgroup theorem is assumed. |
| T01 | Compact connected abelian Lie group iff finite-dimensional torus, including dimension zero | CompactLieTorus.exists_torus_equiv; CompactLieTorus.abelian_iff_torus | LieOneParameter / AbelianParameters / AbelianLattice / LatticeTorus / AbelianTorus |  | PROVED | One-parameter subgroups and lattice quotient | Actual continuous group isomorphism with `Torus (finrank ℝ E)` from the abelian hypothesis; converse by commutativity transport. Includes zero-dimensional model, with no assumed exponential or group-cover existence theorem. |
| T02 | Character lattice of torus is Z^d and representatives are finite character sums | representative_eq_characterSpan; torusCharacterEquiv; torus_representative_laurent | AbelianCharacters / TorusCharacters / TorusLaurent | D-representative; Haar unitarization | PROVED | Joint eigenspaces and Stone–Weierstrass/Haar orthogonality | Exact algebra equivalence for the d-fold unit circle, including d=0. General compact abelian representatives are finite character sums. T01 remains the separate Lie-group classification. |
| T03 | Normalized Haar integral corresponds to Laurent coefficient at zero | torusCoefficientIntegral_laurent; torus_integral_constantTerm | HaarCharacters / TorusLaurent | T02; D-haar | PROVED | Character orthogonality | All coefficients are recovered by integration against inverse characters; the representative Haar functional is exactly the constant term. |
| T04 | Duistermaat–van der Kallen external result must be proved, not postulated | duistermaat_van_der_kallen_one_variable; multivariate target open | OneVariableTorus; OneVariableDvK/* |  | IN PROGRESS | One-variable valuation/partial-fraction substitute | Full one-variable theorem and actual circle Mathieu property proved without additional axioms. Arbitrary rank, already rank two, remains open. See source adaptation and obstruction investigation. |
| T05 | Strict linear separation from convex hull of finite support | support_strict_separation | LaurentSupport | thm:dvdk | PROVED | Manuscript | Mathlib geometric Hahn–Banach and compactness of finite convex hull. |
| T06 | Support of hf^m has separating-functional value≥C+mδ | support_mul_lower_bound; support_pow_lower_bound | LaurentSupport | T05 | PROVED | Manuscript | Support containment, not an incorrect equality of supports. |
| T07 | Archimedean bound yields eventual absence of zero exponent | eventual_constantTerm_zero_of_lower_bound; eventual_constantTerm_zero_of_newton | LaurentSupport | T06 | PROVED | Manuscript | Zero polynomials allowed; all natural m above N. |
| T08 | Zero f/h cases and equivalence with Mathieu subspace on torus | torus_mathieu_iff_constantTerm; zero_laurent_eventual; zero_laurent_multiplier | TorusLaurent | T02; T03 | PROVED | Algebra equivalence and zero identities | Unconditional equivalence of the two Mathieu predicates, without asserting either predicate or assuming DvK. |
| E01 | U V + T² = 1 | Abelian.relation | AbelianAlgebra | D-explicit | PROVED | Manuscript | General commutative ring proof with w*wi=1; applies to unit-circle w. |
| E02 | Defect-one transformed identity | Abelian.defect_one | AbelianAlgebra | E01 | PROVED | Manuscript | Global polynomial identity; no division used. |
| E03 | Printed Laurent expansion exactly equal to P_ab | Abelian.expansion; Abelian.formal_expansion | AbelianAlgebra / AbelianLaurent | D-explicit | PROVED | Manuscript | Also equality in the actual Laurent polynomial algebra. |
| E04 | Four nonzero coefficient polynomials give exact formal spectrum {-1,0,1,2} | Abelian.formal_spectrum | AbelianLaurent | E03 | PROVED | Manuscript | All four coefficient polynomials proved nonzero by evaluation; no claim of fixed-x endpoint spectrum. |
| E05 | t=1-2x² gives normalized weighted CT integral and moment laws | Abelian.weighted_quadratic_substitution; Abelian.weightedCT_pure; Abelian.weightedCT_marked | AbelianConstantTerm / AbelianWitness | E02; H08 | PROVED | Manuscript | Actual formal Laurent coefficients, exact weight and normalization, every positive power and marker; positivity and vanishing ranges also proved. |
| E06 | On SU(2), conjugate entry identities give polynomial Hopf representatives | Abelian.matrix_entry_representatives; Abelian.matrix_entry_pair | SU2Witness | D-hopf; R01 | PROVED | Manuscript | Exact four-entry polynomial formulas; the pair is also constructed in the actual representative algebra. |
| E07 | All entry representatives invariant under maximal torus factor | Abelian.torus_invariance; Abelian.entryP_torus_invariance | AbelianAlgebra | E06 | PROVED | Manuscript | U₀ is also the Q entry representative. |
| E08 | Square-root-free substitution sends A₀,U₀,V₀,T₀ to 1,U,V,T | Abelian.square_root_free; Abelian.square_root_free_pair | AbelianAlgebra | E06 | PROVED | Manuscript | All complex x and nonzero w, including manuscript domain. |
| E09 | Representative independence and equality to actual Mueger–Tuset group-coordinate transform | Abelian.entryTransform_representative_independent; Abelian.haar_entryIntegral_eq_transformedIntegral; Abelian.entryTransform_pair; Abelian.transform_correspondence | EntryTransform / TransformIntegral / TransformPair | E07; E08; E14 (SU(2) specialization) | PROVED | Specialized polynomial interpolation and moment comparison | Formal representative independence; both normalized circle factors; exact radial weight 2x; Hopf pair torus cancellation. |
| E10 | Earlier weighted xz witness has zero pure moments and (-1)^(m-1)/(2(m+1)) marker; spectrum {-1,0,1} | Abelian.weighted_xz_witness; Abelian.earlierXZ_specialize; Abelian.earlierXZ_spectrum | EarlierXZ | beta integral; phase coefficient interpretation | PROVED | Direct binomial/beta proof | Exact formal Laurent polynomial f₀(x²,w), pure and marked weighted integrals, nonzero marker for every m≥1, and exact formal spectrum. No external moment theorem is assumed. |
| E11 | Definitions and admissibility of universal moment and convex-support conjectures | Abelian.UniversalMomentConjecture; Abelian.UniversalConvexSupportConjecture; Abelian.coordinate_weight_admissible; Abelian.mixedIntegral_eq_circle_integral | AbelianConjectures / MixedPhase | E05; E14 (definitions only) | PROVED | Direct witness at N=M=1, δ=x | Arbitrary dimensions, polynomial coefficient ring, actual cube integral and normalized product-circle correspondence; both conjectures refuted. |
| E12 | Zero pure moment sequence has zero limsup growth, contradicting asserted positive growth | Abelian.weightedCT_growth_zero; Abelian.universal_growth_conjecture_false | AbelianConjectures | E05; E11 | PROVED | Manuscript | Actual real limsup of the complex moment norm raised to 1/m; m=0 handled by eventual equality. |
| E13 | Each specified Zwart failure, via implication and contraposition or direct refutation | Zwart.sun_conjecture_2023_contour_false; Zwart.sp_conjecture_2024_contour_false; Zwart.g2_conjecture_2024_contour_false | ZwartSU / ZwartSp / ZwartG2 / ZwartOldSU / ZwartOldSp / ZwartOldG2 | E14 | IN PROGRESS | Direct counterexamples | All three 2025 conjectures and the fractional 2023 SU / 2024 Sp / 2024 G2 conjectures are refuted, with source domains and integrals. The 2023 SO density has the external indexing discrepancy recorded below; its source correspondence remains open. |
| E14 | External Mueger–Tuset Lemma 5.2, Prop 5.3, Conjectures 6.3/6.6, Remark 6.7; Zwart implications: exact definitions and needed results | external_reduction_correspondence | AbelianWitness |  | IN PROGRESS | Source definitions and direct circle-integral proof | Conjectures 6.3/6.6 and growth assertion defined and refuted; Lemma 5.2 and the needed SU(2) polynomial specialization of Prop. 5.3 proved in CircleTransform/TransformIntegral/TransformPair. Direct SU/Sp/G2 counterexamples replace the cited implication proofs; those unused implications are not assumed. Rational-frequency expansion uniqueness is proved in ZwartUniqueness. Exact SO source correspondence remains open. |

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

Current full library build passed (3663 jobs). The verifier moved unchanged to `scripts/verify_mathieu_classification.py`; its output exactly matches `scripts/verify_mathieu_classification.txt` (diff exit 0). H09 now has the complete primitive and integral/substitution correspondence proved; L05 now has the full cyclic submodule, irreducibility, and exact defining matrices. Lemma `lem:haar-pullback` is now fully proved, including actual representative-function witness transport. Final classification and uniform theorem axiom audits are not available because those theorems have not been proved.

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
library. For arbitrary rank, the strongest currently proved downstream statement is
`eventual_constantTerm_zero_of_newton`: once zero is outside the actual Newton
convex hull, every fixed multiplier has eventually zero constant term. The full
one-variable noncancellation theorem and actual circle Mathieu property are now
proved in `OneVariableTorus.lean`; see the adaptation milestone below.

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


Current inventory counts: PROVED=96, TODO=1, IN PROGRESS=8, BLOCKED=5 (110 rows).

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


## Universal abelian conjectures and growth counterexample

The weighted-moment milestone was merged as [PR #9](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/9)
at `f804ef131e9c609c1dee389191a0bfe1d9cc5d5a`, after CI run `35177673659` passed.

The definitions were checked against [Müger–Tuset, arXiv:2410.11622v2, §6](https://arxiv.org/html/2410.11622v2#S6).
`MixedLaurent N M` has multivariate polynomial coefficients and integer-vector
Laurent exponents. `AdmissibleWeight` requires a nonzero monomial with odd exponent
in each polynomial variable. The functional is the actual Lebesgue integral on
the unit cube after normalized circle integration. `MixedPhase.lean` proves this
product-circle/constant-term correspondence for every N and M, including zero.
It also identifies the phase monomials with actual integer powers on unit circles;
finite-product Fubini and finite sums justify all integrations. Cube integrability
is proved for every coefficient polynomial and admissible weight.

A ring equivalence embeds the checked Laurent witness at N=M=1. The exact integral
correspondence is `mixedIntegral x (singleMixed f) = weightedCT f / 2`.
The exponent-one weight is proved admissible. The nonzero constant coefficient
puts zero in the actual Newton convex hull. These facts refute both universal
conjectures. The real limsup of the 1/m-th powers of the moment norms is zero,
refuting the stronger growth assertion as well. The m=0 term is irrelevant by
proved eventual equality, not by changing the sequence's definition.

This completes E11 and E12. The named abelian-reductions corollary remains
IN PROGRESS: its additional assertions about the specified Zwart implications
are not proved. E14 likewise retains the unproved square-root-free transform
correspondence and Zwart results. No missing external theorem is assumed.

Abelian-conjecture validation: `lake build` passed (3631 jobs); source audit passed
for 36 Lean files. Whole-namespace audit passed for 683 declarations (559 theorem
constants), with only the three approved foundations. There are 263 explicit
theorem/lemma declarations in 33 mathematical modules. The ledger has 57/110
obligations proved. The verifier output matches exactly, the remaining target
statements type-check, and the manuscript is unchanged. The final whole-paper
correspondence audit is still outstanding.


## Projected Haar geometry and transfer from a supplied defining doublet

The universal abelian counterexamples were merged as [PR #10](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/10)
at `2a479e5cbc39a8bd64360caa82cef80f9786cdbf`, after CI run `35178382911` passed.

`Projection.lean` proves the unitary invariant-complement and projection identities,
then constructs the two coordinates through an isometric identification W≃ℂ².
The coordinate map is continuous, equivariant, lies in the Euclidean unit ball,
and takes the identity to (1,0). Inner-product formulas explicitly account for
Lean’s convention that the second argument is linear.

`ProjectedHaar.lean` proves the radial-pushforward lemma for these constructed
coordinates, given the manuscript’s standing defining-doublet data. It proves
probability normalization, compact support, the Euclidean ball bound, actual
SU(2) invariance, and strictly positive mass outside zero. It also transports
the radial moment formulas back to the original group by the map-integral theorem.

`ProjectedRepresentatives.lean` constructs both coordinate functions as coefficients
of the actual finite-dimensional representation. Algebra and conjugation closure
then construct all six Hopf quantities in the representative algebra. A is a
nonnegative real-valued function, equals one at the identity, and is nonzero.
`DoubletWitness.lean` proves the exact pure/marked formulas, vanishing and positive
ranges, and Mathieu failure for this supplied representation data.

This closes D-Phi and L08–L11, and the radial-pushforward lemma with its standing
inputs. It does NOT close the simple-group theorem: the universal construction
of a fundamental representation and its root doublet (L02/L06) remains unproved.
The hypotheses in `unitary_doublet_not_mathieu` are explicit representation and
intertwining data, not an asserted existence theorem. No conditional theorem is
presented as the manuscript’s general simple-group or classification theorem.

Projection/transfer validation: `lake build` passed (3635 jobs); source audit
passed for 40 Lean files. Whole-namespace audit passed for 781 declarations
(640 theorem constants), with only the three approved foundations. There are
309 explicit theorem/lemma declarations in 37 mathematical modules. The ledger
has 63/110 obligations proved. The verifier output matches exactly, the remaining
targets type-check, and the manuscript remains unchanged.


## Cyclic sl₂ module and root-map faithfulness

The projected-Haar and representative-transfer milestone was merged as
[PR #11](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/11)
at `8a5daa618057255f17694cf84ea4095fd64348de`, after CI run `35179342273` passed.

`RootDoubletModule.lean` constructs the actual Lie submodule generated by a
primitive highest-weight-one vector in an existing finite-dimensional module.
Its basis is (v,Fv), its dimension is two, and every Lie submodule of it is
either zero or the whole doublet. The matrix of αE+βF+γH in this basis is
[[γ,α],[β,−γ]], proving the defining two-dimensional algebraic action. This
completes L05; it does not supply the ambient fundamental representation.

`RootDoubletFaithfulness.lean` proves that a supplied group homomorphism acting
by the defining SU(2) action on an identified doublet is injective. It also
proves that conjugation by any unitary 2×2 matrix preserves the entire SU(2)
subgroup, with both image inclusions. This completes the faithfulness and
coordinate-change step L07 with its standing L06 inputs. The root homomorphism
and its integrated defining action have not been constructed.

Cyclic-doublet validation: `lake build` passed (3637 jobs); source audit passed
for 42 Lean files. Axiom audit passed: 804 project declarations, 658 theorems.
Only propext, Classical.choice, and Quot.sound occur in dependencies. There
are 321 explicit theorem/lemma declarations in 39 mathematical modules. The
ledger now has 65/110 obligations proved (33 TODO, 6 IN PROGRESS, 6 BLOCKED).
The verifier output matches exactly, the remaining targets type-check, and
the manuscript remains unchanged. Next: Haar averaging for L03, then center
descent; fundamental representation/root integration and Duistermaat–van der
Kallen remain major unproved dependencies.


## Haar unitarization

The cyclic-doublet milestone was merged as
[PR #12](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/12)
at `5e74cda1c982901e30b1b07756de755a30c2af2b`, after CI run `35180222690` passed.

`HaarUnitarization.lean` constructs the Haar average of an initial Hermitian
form and proves strict positivity using continuity and positivity of Haar on
nonempty open sets. Right Haar invariance proves invariance of the average.
A separate carrier carries the induced norm, avoiding a competing norm on
the original type. In finite dimension its linear identification is a continuous
linear equivalence. The constructed group homomorphism takes values in actual
linear isometric equivalences, intertwines the original action, and has
continuous orbits.

For an arbitrary finite-dimensional complex normed representation, Euclidean
coordinates provide the initial inner product without assuming its original
norm is induced by an inner product. The unitary model pulls back to a continuous
positive-definite invariant Hermitian form on the original vector space. This
completes L03. The convention is linearity in the second variable; the coordinate
wrappers elsewhere already account for the manuscript's opposite convention.

Next: use mathlib's algebraically closed Schur lemma for the center action and
prove the balanced tensor representation factors through the central quotient.
No assertion of fundamental representation or root-homomorphism existence is
added by unitarization.

Unitarization validation: `lake build` passed (3638 jobs); source audit passed
for 43 Lean files. Axiom audit passed: 892 project declarations, 722 theorems.
Only the three approved foundations occur. There are 332 explicit theorem/lemma
declarations in 40 mathematical modules. The ledger records 66/110 obligations
proved (32 TODO, 6 IN PROGRESS, 6 BLOCKED). The verifier output matches exactly,
the remaining target statements type-check, and the manuscript is unchanged.


## Center descent

Haar unitarization was merged as
[PR #13](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/13)
at `c95475244ce6240dad0649d7f656d68ae928f2e4`, after CI run `35181312147` passed.

`CenterDescent.lean` applies mathlib's algebraically closed Schur lemma to the
central intertwining endomorphism. In a nontrivial irreducible unitary
representation the scalar has modulus one, by comparing the norm of a nonzero
vector. The projection coordinates transform by this same scalar, and the
proved phase-balance identities give invariance of all six Hopf functions.

The tensor product with the conjugate matrix representation is identity on
every unit scalar action. `MatrixRepresentation.descend` constructs a quotient
group homomorphism and proves continuity from the quotient topology. The
descended balanced coefficients pull back exactly to zᵢ conjugate(zⱼ). Their
algebraic combinations construct A, τ, u, v, P, Q in the actual representative
algebra on the quotient. The final `center_descent` wrapper chooses a basis of
the supplied unitary space, identifies its coefficients with the projected
coordinates, and proves all six pullback identities for every central subgroup.
Normality follows from centrality, with no additional assumption.

This completes Z01–Z04 and Lemma `lem:center-descent` with its manuscript
standing representation data. The simply connected representation-existence
step and the covering theorem for general compact simple central forms remain
unproved; Corollary `cor:simple-central-forms` is not claimed as a general
existence theorem.

`QuotientWitness.lean` transports the exact marker tower through the actual
quotient homomorphism. It constructs nonnegative nonzero A, proves every pure
and marked moment formula with normalized quotient Haar, proves both index
ranges, and derives failure of the Mathieu property. This makes the central-form
corollary IN PROGRESS: transfer is complete, but the universal representation
and covering inputs are still unproved. Next: group structure and classical
distribution obligations, while preserving the separate foundational gaps.

Center-descent validation: `lake build` passed (3647 jobs); source audit passed
for 45 Lean files. Axiom audit passed: 918 project declarations, 744 theorems.
Only propext, Classical.choice, and Quot.sound occur in dependencies. There are
42 mathematical modules. The ledger records 71/110 obligations proved
(26 TODO, 7 IN PROGRESS, 6 BLOCKED). The verifier output matches exactly,
remaining target statements type-check, and the manuscript remains unchanged.


## Beta moments and classical numerical expressions

Center descent and the central-quotient tower were merged as
[PR #14](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/14)
at `be63d30c0a186e8322428840d5452887bb4d186b`, after CI run `35181999307` passed.

`BetaMoments.lean` proves natural moments for mathlib's actual `betaMeasure`
with arbitrary positive real shape parameters. Multiplication of the density
by xᵏ shifts its first parameter; probability normalization gives the beta
function ratio. Integrability of every moment is proved. Gamma recurrence
converts the ratio to a quotient of finite rising products, and integer
parameters give the ascending-factorial formula. In particular Beta(2,n−2)
has moment (2)ₖ/(n)ₖ for every n≥3. This completes C04.

`ClassicalConstants.lean` checks all nine printed rational expressions and
proves the three SU(2) values as actual representative Haar moments. Its
`classicalMomentFormula` is explicitly a numerical expression; no identification
with Haar moments for higher-dimensional SU(n) or Sp(n) is asserted. C07 and
the classical-closed-forms proposition are IN PROGRESS until those distribution
correspondences are established.

Next: prove the classical first-column sphere distributions and projected
radial beta laws, or use an equivalent invariant-moment proof with the exact
measure correspondence. Gaussian normalization (C02), sphere beta law (C03),
and symplectic transitivity (C05) remain explicit obligations.

Beta-moment validation: `lake build` passed (3650 jobs); source audit passed
for 47 Lean files. Axiom audit passed: 945 project declarations, 770 theorems.
Only the three approved foundations occur. The library has 44 mathematical
modules; the ledger records 72/110 obligations proved (23 TODO, 9 IN PROGRESS,
6 BLOCKED). The verifier matches exactly, remaining targets type-check, and
the mathematical manuscript is unchanged.


## Current continuation: classical sphere geometry

The beta-moment milestone was merged as
[PR #15](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/15)
at `f3d2d9ea6837c2c52d573a0ab097cdbcaa4658e8`, after CI run `35182461284` passed.

The current branch is `formalization/classical-sphere`.
`ClassicalSphereGeometry.lean` proves existence of a unitary matrix with any
prescribed unit first column. For n≥2 a diagonal unitary correction in the
second column makes the determinant one while preserving the first column.
The actual SU(n) defining homomorphism into Euclidean linear isometric
equivalences is constructed, with joint continuity proved entrywise. C01 is
IN PROGRESS; the Haar/surface correspondence is not yet proved.

Next concrete steps: establish compactness and the topological-group instances
for general SU(n); use the prescribed-column result to obtain a transitive
action on the unit sphere. Generalize the cone-surface invariance proof from
`SphereSymmetry.lean` to Euclidean complex n-space, normalize its actual
`volume.toSphere` measure, and apply `measurePreserving_transitive_orbit`.
Mathlib `Matrix.entrywise_sup_norm_bound_of_unitary` and `isClosed_unitary`
should supply compactness via a closed bounded matrix set. The existing
`Matrix.continuous_uncurry_toEuclideanCLM` caused expensive elaboration here;
the checked entrywise finite-sum proof avoids that issue.

No root-existence, covering, DvK, higher-dimensional sphere beta-law, or
Gaussian-normalization obligation is considered closed by this geometry.

Continuation checkpoint: `lake build` passed (3663 jobs); source audit passed
for 48 Lean files. Axiom audit passed: 964 project declarations, 788 theorems.
Only the approved foundations occur. The new geometry is uncommitted on the
current feature branch, ready to be extended into the C01 measure correspondence
before the next natural milestone. Ledger counts: 72 PROVED, 22 TODO,
10 IN PROGRESS, 6 BLOCKED (110 obligations).

## SU(n) Haar first-column correspondence

`ClassicalTopology.lean` supplies compactness and the topological-group
structure for every actual special unitary matrix group. Closedness follows
from unitarity and determinant one; the unitary entry bound gives boundedness.
`NormalizedSphere.lean` generalizes the existing cone-surface argument to
arbitrary finite-dimensional real inner-product spaces. Its normalized measure
is a probability measure in nonzero dimension and is preserved by every real
linear isometry.

`ClassicalOrbit.lean` constructs the actual SU(n) sphere action and proves
continuity and transitivity for n≥2. The existing transitive-orbit averaging
theorem then identifies normalized Haar under the first-column map with the
normalized Euclidean sphere measure. The coordinate lemma verifies that the
map is exactly the matrix first column. This completes C01, with no hypothesis
assuming an invariant distribution. C02 and C03 (Gaussian normalization and
radial beta law) and C05 (symplectic transitivity) remain open.

The earlier continuation checkpoints above record historical states. Current
inventory: 73 PROVED, 22 TODO, 9 IN PROGRESS, 6 BLOCKED, 110 total. The library
contains 49 mathematical modules plus its umbrella. No change to the manuscript
or verification mathematics was made.

SU(n) milestone validation: `lake build` passed (3667 jobs). Source audit
passed for 51 Lean files. Namespace axiom audit passed for 1006 declarations
and 822 theorem constants, depending only on propext, Classical.choice, and
Quot.sound. The exact verifier output matches the checked-in output, outstanding
target statements type-check, and the manuscript is byte-for-byte unchanged.

## Gaussian normalization correspondence

The SU(n) sphere milestone was merged as
[PR #16](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/16)
after CI run `35183713349` passed. The current branch is
`formalization/gaussian-sphere`.

`GaussianSphere.lean` defines a measurable normalized direction with an arbitrary
fixed sphere value at zero. It proves standard Gaussian measure has no atoms
in a nontrivial finite-dimensional real inner-product space, using positive
variance of a nonzero continuous linear functional. Normalization commutes
with isometries off zero, so Gaussian isometry invariance gives invariant
sphere pushforward. Transitive SU(n) orbit averaging identifies that pushforward
with the actual normalized Euclidean sphere measure for n≥2.

The final theorem starts from the product of 2n independent real N(0,1)
variables, groups them into n complex coordinates, and proves the exact
normalized sphere pushforward. Its grouping is verified using the product
orthonormal basis formed from 1 and i. The common Gaussian scale has no effect
on normalization. This completes C02 for all dimensions used by the manuscript.
No Dirichlet or beta law has been assumed. C03 remains open: mathlib contains
beta and gamma densities but does not supply the needed normalized gamma or
Dirichlet distribution correspondence directly. The next step is to derive
that correspondence or a faithful invariant-moment substitute, keeping every
measure normalization explicit.

Current inventory: 74 PROVED, 21 TODO, 9 IN PROGRESS, 6 BLOCKED (110 total).

Gaussian milestone validation: `lake build` passed (3848 jobs). Source audit
passed for 52 Lean files. Namespace axiom audit passed for 1023 declarations
and 837 theorem constants, with only propext, Classical.choice, and Quot.sound.
The verifier output matches exactly, outstanding targets type-check, and the
manuscript remains unchanged. The library has 49 mathematical modules.

## Gamma/beta distribution infrastructure

Gaussian normalization was merged as
[PR #17](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/17)
at `de5c32981c0cda57cd3f482af5e916b59e3a4075`, after CI run `35184138107` passed.
The current branch is `formalization/gamma-beta`.

`GammaBeta.lean` proves the split map parametrizes the positive quadrant,
computes its derivative and determinant, and applies mathlib's Lebesgue
change-of-variables theorem. A real-density factorization proves the exact
product probability law. The inverse ratio/sum map then proves that independent
Gamma(a,r) and Gamma(b,r) variables yield independent Beta(a,b) ratio and
Gamma(a+b,r) sum, for arbitrary positive real parameters. Both marginal laws
are extracted. Boundary sets and density restrictions are proved explicitly.

This is progress on C03, not yet the sphere beta law. Next: prove squared real
Gaussians have Gamma(1/2,1/2) law; combine pairs and finite sums, then use the
checked Gaussian-to-sphere correspondence to obtain the first-two-coordinate
Beta(2,n−2) law and the Dirichlet normalization model. Current inventory:
74 PROVED, 20 TODO, 10 IN PROGRESS, 6 BLOCKED (110 total).

Gamma/beta validation: `lake build` passed (3854 jobs). Source audit passed
for 53 Lean files. Namespace axiom audit passed for 1046 declarations and
857 theorem constants, with only the three approved foundations. The verifier
output matches exactly, outstanding statements type-check, and the manuscript
is unchanged. There are 50 mathematical modules.

## Sphere Dirichlet/beta laws and SU(n) radial moments

Gamma/beta infrastructure was merged as
[PR #18](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/18)
at `a60399f6c73cf0af0574d07b97794cbf9280dc90`, after CI run `35184845276` passed.
The current branch is `formalization/gaussian-gamma`.

`GaussianSquare.lean` proves the actual squared N(0,1) law is
Gamma(1/2,1/2), using evenness, positive-half-line substitution y=x², and
Gamma(1/2)=sqrt(pi). A pair of independent squares has Gamma(1,1/2) law.
`GaussianRadii.lean` uses the product-measure curry theorem to group real and
imaginary coordinates and proves that squared moduli of the actual complex
Euclidean standard Gaussian have independent Gamma(1,1/2) laws.

`FiniteGamma.lean` proves arbitrary finite sums and block ratios of independent
gamma coordinates. `GammaScale.lean` proves positive scaling of shape-one
gamma variables to unit rate. `SphereBeta.lean` then identifies the actual
normalized sphere coordinate masses with Dirichlet(1,…,1), defined by its
standard normalized independent unit-rate gamma construction. The common-rate
conversion is proved; it is not an implicit convention change. Coordinate
masses are nonnegative and sum to one. Every nonempty proper block has the
corresponding beta law, in particular Beta(2,n−2) for the first two coordinates
when n≥3. This completes C03.

The manuscript-facing SU(n) radial quantity is explicitly
A(g)=normSq(g[0,0])+normSq(g[1,0]). Its actual normalized Haar pushforward is
Beta(2,n−2), and every natural moment is (2)ₖ/(n)ₖ. The n=2 endpoint A=1 is
checked directly, so the moment theorem holds for all n≥2. Integrability of
all radial moments is explicit. C06 is IN PROGRESS because the separate
Sp(1) identification is not yet formalized.

Next: connect the SU(n) defining first-two-coordinate pair to the existing
radial marker theorem (construct the block SU(2) action and representative
functions), yielding the classical marked-moment formulas and the SU(3)/SU(4)
printed examples as actual Haar moments. Sp(n) transitivity and the major
root-existence/DvK/general Lie structure gaps remain open. Current inventory:
75 PROVED, 19 TODO, 10 IN PROGRESS, 6 BLOCKED (110 total); 55 mathematical modules.

Sphere-beta milestone validation: `lake build` passed (3923 jobs); source
audit passed for 58 Lean files. Namespace axiom audit passed for 1122 project
declarations and 926 theorem constants. All dependencies are limited to
propext, Classical.choice, and Quot.sound. Exact verifier output matches,
outstanding target statements type-check, and the manuscript remains unchanged.

## Complete SU(n) defining marker formulas

Sphere Dirichlet/beta laws and radial Haar moments were merged as
[PR #19](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/19)
after CI run `35186105271` passed. The current branch is
`formalization/su-classical-markers`.

`ClassicalSU.lean` constructs the continuous injective block embedding
SU(2)→SU(2+n), proves the first-two-entry projection equivariant, and constructs
its coordinate functions from the actual defining matrix representation.
The fixed A, P, Q are genuine representative functions and agree pointwise
with the manuscript Hopf quantities. The existing radial theorem and actual
radial Haar moments prove the entire SU(n) closed form. The exact marker tower,
both index ranges, and failure of the Mathieu property for every n≥2 are
proved. The manuscript-facing `specialUnitary_closed_forms` wrapper uses n≥2,
with pointwise identification of A, P, and Q. All nine printed values for
SU(2), SU(3), and SU(4) are now actual representative Haar moments.

A generic witness lemma was added to `Haar.lean` to expose the already-proved
Mathieu witness criterion at the representative-algebra level. This avoids
repeated elaboration of the large concrete matrix-group algebra instances;
it introduces no hypothesis beyond the explicit pure/marked witness facts.

The classical-closed-forms proposition and C07 remain IN PROGRESS because they
also assert Sp(n) formulas and the Sp(2) interpretation of the third numerical
row. No general simple-group/root existence result is inferred from the
explicit SU(n) embedding. Counts remain 75 PROVED, 19 TODO, 10 IN PROGRESS,
6 BLOCKED (110 total), with 56 mathematical modules.

Next: the compact symplectic defining action and first-column sphere law.
A possible specialized construction is to group complex coordinates into
quaternionic pairs, send each pair to its nonnegative real length using the
already-built SU(2) matrix, then use an orthogonal real matrix to realize the
vector of lengths as a first column. Paired SU(2) blocks and the duplicated
real orthogonal action preserve the standard symplectic form and unitarity.
This may establish Sp(n) transitivity without a general quaternionic
inner-product-space theory. The first-simple-root marker embedding must match
the first two complex defining coordinates (with Sp(1) handled separately).

SU(n) marker validation: `lake build` passed (3924 jobs). Source audit
passed for 59 Lean files. Namespace axiom audit passed for 1180 declarations
and 976 theorem constants, using only propext, Classical.choice, and Quot.sound.
The exact verifier matches, outstanding targets type-check, and the manuscript
is unchanged. This milestone adds no fully closed ledger row because the
classical proposition and numerical row also require Sp(n).


## Compact symplectic geometry and radial moments

The SU(n) representative-marker milestone merged in
[PR #20](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/20)
at `95dc24f93050a7b122107621b2235151aebf8b61`, after CI run `35187036184` passed.

`CompactSymplectic.lean` defines the actual compact unitary symplectic matrix
group as a closed subgroup of SU(n+n). Mathlib's `SymplecticGroup.det_eq_one`
proves that the determinant-one ambient group imposes no extra condition:
every unitary symplectic matrix lifts, and its underlying matrix is unchanged.
The subgroup is compact and inherits its topological group structure.

A constructive substitute for quaternionic orthonormal basis extension proves
sphere transitivity. For a unit vector, take the nonnegative length of each
complex coordinate pair. Extend this real unit vector to a real orthonormal
basis. The resulting orthogonal matrix, doubled and complexified, supplies
the pair lengths; independent SU(2) matrices supply the actual pairs. The
previous equal-radius SU(2) orbit theorem handles zero pairs, so no division
by a potentially zero radius occurs. Both matrix components are proved
unitary and symplectic, and their product has exactly the prescribed first
column. No transitivity or representation existence assumption is introduced.

`SymplecticOrbit.lean` identifies actual normalized Haar first-column measure
with the normalized Euclidean sphere measure. The already-proved sphere beta
law yields Beta(2,2n-2) for n≥2 and all radial moments (2)ₖ/(2n)ₖ. For n=1,
A is identically one. The rank-one compact symplectic subgroup is proved to
be all SU(2), with an explicit continuous multiplicative equivalence and
continuous inverse. This closes C05 and C06.

Current inventory: 77 PROVED, 18 TODO, 9 IN PROGRESS, 6 BLOCKED (110 total),
with 58 mathematical modules. The classical marker proposition and C07 remain
open for Sp(n): next construct the first-simple-root SU(2) block inside the
unitary-to-symplectic embedding for n≥2, use the rank-one equivalence for n=1,
and connect the actual representative P,Q functions to the radial formulas.
The general root-existence, DvK, and compact Lie structure gaps remain open.

Compact symplectic validation: `lake build` passed (3927 jobs), source audit
passed for 61 Lean files, and namespace axiom audit passed for 1265 declarations
and 1047 theorem constants. Only propext, Classical.choice, and Quot.sound
occur. Outstanding targets type-check, exact verifier output matches, and
the manuscript remains unchanged. Review checked the unitary/symplectic
correspondence, zero-radius pairs, both positive-rank ranges, first-column
indices, the rank-one equivalence, and the probability normalizations.


## All classical defining-representation marker formulas

The compact symplectic sphere milestone merged in
[PR #21](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/21)
at `21325a71e08946d8bbb309b51d8a71762da2ee7a`, after CI run `35188095557` passed.

`ClassicalSp.lean` constructs the continuous injective SU(2) subgroup acting
on the first two defining complex coordinates for Sp(n), n≥2. It doubles
the SU(n) block as diag(A, conjugate A); membership in the compact symplectic
group is proved by the earlier matrix construction. Direct multiplication
proves first-two-coordinate projection equivariance. These are the standard
first-simple-root coordinates in the manuscript's defining representation;
the proof uses the explicit matrices and requires no general root integration
theorem. The projection entries are actual finite-dimensional continuous
matrix coefficients, and the Hopf polynomials give actual representatives.

Radial transfer gives the pure vanishing and entire fixed-marker tower.
The sphere-derived radial moments give the exact c_m binomial times
(2)_(4m+s)/(2n)_(4m+s) formula, positivity for 1≤s≤m, and zero for s>m.
The rank-one formula is pulled back from SU(2) through the proved continuous
Sp(1)=SU(2) equivalence using the normalized Haar/representative pullback
identity. The manuscript wrapper quantifies over every n≥1 and identifies
A, P, and Q pointwise with the first-column Hopf formulas. The three Sp(2)
printed values are actual Haar integrals. Failure of the Mathieu property is
also proved for every positive-rank compact Sp(n).

Together with `ClassicalSU.lean`, this completes the named classical
closed-forms proposition and C07. Current inventory is 79 PROVED, 18 TODO,
7 IN PROGRESS, 6 BLOCKED (110 total), with 59 mathematical modules. The general
classification and arbitrary nonabelian uniform theorem are still unproved.
Next: return to the remaining manuscript correspondence and structural
obligations; explicit classical groups do not discharge the general
root-existence or compact Lie decomposition steps, nor the DvK torus direction.

Sp(n) marker validation: `lake build` passed (3928 jobs); source audit passed
for 62 Lean files; namespace axiom audit passed for 1319 declarations and
1094 theorem constants, using only the three approved foundations. The exact
verifier matches, outstanding targets type-check, and the manuscript is
unchanged. Review checked matrix coefficients, first-simple-root coordinate
blocks, all m/s/rank ranges, the rank-one pullback, and the printed constants.
The next independent tractable obligation is E10, the earlier weighted xz
witness f₀(t,w)=(1-w⁻¹)((1-t)+tw), with t=x². A specialized binomial/beta
calculation should prove its two moments and three-element spectrum without
using any external result as an assumption.


## Earlier weighted xz witness

The full classical marker milestone merged in
[PR #22](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/22)
at `db690d5beb6fda0ae1d2f36f5644d3aae7c353f3`, after CI run `35188571769` passed.

`EarlierXZ.lean` proves the earlier witness quoted before the explicit Hopf
transform proposition. Its formal Laurent polynomial is exactly
(1-w⁻¹)((1-x²)+x²w), with exact coefficient polynomials x²-1, 1-2x², x²
and spectrum {-1,0,1}. Specialization agrees with f₀(x²,w).

The proof expands the affine factor in the Bernstein basis and uses the
actual complex beta integral and gamma factorial identities to integrate
each term. A Laurent geometric sum telescopes. Elementary support bounds and
the lowest coefficient of (1-w⁻¹)^m give zero pure moments and coefficient-one
moment (-1)^(m-1)/(m+1). The checked substitution t=x² introduces the actual
weight x and factor 1/2, producing exactly the printed marked integral
(-1)^(m-1)/(2(m+1)), proved nonzero for every m≥1. This is a direct specialized
proof of the cited earlier moment theorem, with no external assumption.

E10 is PROVED. Current inventory: 80 PROVED, 17 TODO, 7 IN PROGRESS, 6 BLOCKED
(110 total), with 60 mathematical modules. Next tractable correspondence:
H05, the full Hopf-coordinate surface-measure formula. Existing ingredients
include phase invariance, the complete sphere moments, and the new sphere
Dirichlet/beta law. A route is two independent phase averages followed by the
first-coordinate mass distribution, or a compact Stone–Weierstrass argument
identifying the coordinate pushforward from all mixed moments. The exact
full coordinate density is not yet claimed; the general DvK/root/compact Lie
structure obligations remain unresolved.

Earlier xz validation: `lake build` passed (3929 jobs); source audit passed
for 63 Lean files; namespace axiom audit passed for 1365 declarations and
1136 theorem constants. Only propext, Classical.choice, and Quot.sound occur.
Outstanding targets type-check, exact verifier output matches, and the
manuscript is unchanged. Review checked the Bernstein normalization, the
coefficient-one shift for the fixed w⁻¹ multiplier, the factor 1/2 from
substitution, nonvanishing, and formal (rather than pointwise-specialized)
spectrum.


## Full Hopf-coordinate surface measure

The earlier weighted xz milestone merged in
[PR #23](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/23)
at `bf764ea7e8d55fce9d988c44ced80b8f1c53a38a`, after CI run `35189283703` passed.

`SphereDetermination.lean` proves that all mixed coordinate/star-coordinate
moments determine a finite Borel measure on the sphere. Conjugating one
coordinate is a real linear isometry preserving surface measure; together
with the existing diagonal SU(2) phase argument, this proves zero integral
for every monomial whose two coordinate exponents are not individually
balanced. The span of all coordinate monomials is a point-separating star
algebra. Stone–Weierstrass, continuity of integration in the uniform norm,
and regular-measure uniqueness extend agreement on moments to equality of
measures. No moment-determination assumption is introduced.

`HopfCoordinateMeasure.lean` constructs the actual product-probability unit
cube parametrization (sqrt(u) exp(2πiα), sqrt(1-u) exp(2πiβ)). Its monomial
integrals factor into two integer-frequency integrals and a beta integral.
They agree exactly with the proved Euclidean sphere moments, so the
pushforward measure equals `surfaceMeasure`. The unit-cube integral identity
holds for every continuous function on the sphere. Affine interval changes
of variables give the manuscript formula for continuous ambient test
functions, with τ=2u-1 and the exact density dτ dα dβ/(8π²). Thus this is a
measure correspondence, not merely verification of a selected integrand.
The endpoint-null and coordinate-surjectivity facts were already proved.

H05 is PROVED. Current inventory: 81 PROVED, 17 TODO, 6 IN PROGRESS, 6 BLOCKED
(110 total), with 62 mathematical modules. All Hopf/sphere/radial obligations
are now checked. The existing Hopf marker proof remains the invariant-moment
substitution; the new result independently supplies its original coordinate
measure correspondence. Next: the external square-root-free group-coordinate
transform correspondence (E09/E14) and the remaining torus/Lie structure
obligations. DvK and the general root/cover/decomposition results remain open.

Hopf-coordinate validation: `lake build` passed (3942 jobs); source audit
passed for 65 Lean files; namespace axiom audit passed for 1428 declarations
and 1190 theorem constants, using only propext, Classical.choice, and
Quot.sound. Outstanding targets type-check; the verifier reproduces its
checked-in output exactly; the manuscript remains unchanged. Self-review
checked finite-measure moment determination, both independent phase balances,
actual pushforward equality, Fubini integrability, and all three interval
normalization factors.

## SU(2) polynomial transform correspondence in progress

The full Hopf-coordinate milestone merged in
[PR #24](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/24)
at `44b85f8a4fa2169ddb46f5e265d0ae827320c43a`, after CI run `35190607210` passed.
The current branch is `formalization/su2-polynomial-transform`.

`CircleTransform.lean` checks Müger–Tuset Lemma 5.2 for arbitrary entry
polynomials and arbitrary radial weights. The circle integral kills monomials
with unequal first/fourth exponents; equal exponents combine the two square
roots into 1-x². These are actual normalized circle and interval integrals.

`EntryTransform.lean` proves representative independence as an equality of
formal Laurent polynomials in ℂ[x][w,w⁻¹]. A Laurent polynomial vanishing on
the unit circle is zero (clear negative powers and use polynomial root
finiteness). Scaling the first sphere coordinate by a unit-circle element
preserves SU(2); Laurent interpolation extends this to nonzero complex
scalings. Choosing the real square-root radius gives the square-root-free
substitution on 0<x<1; continuity handles endpoints. A second polynomial
interpolation in the real radius proves the formal coefficient identities.
This replaces the cited general complexification-density argument with an
elementary specialized proof, without additional assumptions.

Both new modules build. E09/E14 remain open pending the actual Haar integral
correspondence, including the right torus factor and radial normalization
2x. A scratch proof in `/tmp/mathieu-transform-integral.lean` compares every
entry monomial: the two phase averages enforce first=fourth and second=third
exponents, and the remaining weighted integral is a beta moment. Extend by
polynomial linearity, then specialize to the torus-invariant Hopf pair. The
full general-group Prop. 5.3 and Zwart reductions retain their separate Lie
structure dependencies. No manuscript changes; full milestone audits pending.


The SU(2) polynomial correspondence is now complete locally.
`TransformIntegral.lean` compares the actual Haar integral with the
square-root-free integral for every polynomial in the four matrix entries.
The two independent circle frequencies enforce first=fourth and second=third
exponents. The remaining integral is the beta moment, with the exact radial
weight 2x. Both functionals are additive on entry polynomials, so monomial
agreement extends to every polynomial. All integrability and continuity
requirements are proved.

`TransformPair.lean` proves right torus invariance of both entry polynomials,
identifies their images as the formal Laurent polynomials `formalP` and
`formalQ`, and proves `transform_correspondence` for all natural m,s:
the actual representative Haar integral of Q^s P^m equals the weighted
constant term of formalQ^s formalP^m. `CircleTransform.lean` also identifies
actual unit-circle Laurent evaluation with the constant term. The phase
normalizations are probability integrals on [0,1]; the radial factor is 2x.

E09 and `prop:explicit-abelian-SU2` are PROVED. Current inventory: 83 PROVED,
16 TODO, 5 IN PROGRESS, 6 BLOCKED (110 total), with 66 mathematical modules.
This proves the needed SU(2) polynomial specialization of the cited external
transform theorem; it does not assert the general compact Lie-group
parametrization. E14 retains its general-group/Zwart obligations. DvK and the
general root/cover/decomposition results remain unresolved. Next: audit and
merge this milestone, then continue the torus/Lie/external-reduction work.

SU(2) transform validation: `lake build` passed (3956 jobs); source audit
passed for 69 Lean files; namespace axiom audit passed for 1531 declarations
and 1279 theorem constants. Dependencies are only propext, Classical.choice,
and Quot.sound. Outstanding targets type-check, the verifier reproduces its
checked-in output exactly, and the manuscript remains unchanged. Self-review
checked the formal (not merely pointwise) representative equality, endpoint
continuity, both phase balances, Haar/sphere identification, radial beta
normalization, and the final representative-function wrapper for all m,s.


## Compact abelian characters and exact torus/Laurent correspondence

The SU(2) transform milestone merged in
[PR #25](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/25)
at `f8f07c6a8ede0e2c18dfc28889b91838b6a17c21`, after CI run `35192154028` passed.
The current branch is `formalization/abelian-character-decomposition`.

`AbelianCharacters.lean` proves that representative functions on any compact
abelian group are exactly finite complex linear combinations of continuous
characters. Haar unitarization supplies an actual invariant inner product.
For each group operator U, the operators U+U⁻¹ and i(U-U⁻¹) are symmetric;
all of these operators commute. Mathlib's joint-eigenspace theorem says their
joint eigenspaces span the finite-dimensional space. Reconstructing U gives
a scalar action on each joint space. A nonzero vector proves that scalar is
a continuous character. Submodule induction yields the finite character
expansion for every coefficient; conversely, each character is an actual
one-dimensional continuous representation. No semisimplicity or character
classification is assumed.

`HaarCharacters.lean` proves continuity of Haar integration and orthogonality
of continuous characters using group translation. The inverse character is
formed with group inversion; no unit-circle classification is needed.

`TorusCharacters.lean` defines the actual d-fold product of unit circles,
constructs all integer Laurent characters, and proves these form a dense
star algebra by Stone–Weierstrass. Haar orthogonality then forces any
continuous complex character to be one of these integer monomials. Laurent
interpolation on one coordinate proves uniqueness. The dimension-zero case
is included. The existing two circle-interpolation lemmas were extracted
unchanged from `EntryTransform.lean` into `LaurentInterpolation.lean` for
reuse; the SU(2) proof still imports and uses them.

`TorusLaurent.lean` constructs an algebra map from the complex multivariate
Laurent algebra to actual continuous torus functions. Character orthogonality
recovers every coefficient, proving injectivity. The character-span theorem
proves that the image is exactly the repository's representative-function
algebra. This gives `torus_representative_laurent`, an actual algebra
equivalence, and `torus_integral_constantTerm`, equality of the actual Haar
functional with the Laurent constant term. The exact Mathieu predicates are
proved equivalent, and both zero cases are checked.

T02, T03, and T08 are PROVED. Current inventory: 86 PROVED, 13 TODO,
5 IN PROGRESS, 6 BLOCKED (110 total), with 71 mathematical modules.
The torus Mathieu predicate itself remains unproved: DvK is still needed to
turn vanishing positive moments into Newton-hull avoidance. T01 (every compact
connected abelian Lie group is a finite-dimensional torus) and all general
root/cover/decomposition obligations also remain open. The manuscript has
not changed. Next: complete audits and merge, then continue the minimal DvK
and general Lie/external-reduction obligations.

Abelian/torus validation: `lake build` passed (3964 jobs); source audit passed
for 74 Lean files; namespace axiom audit passed for 1659 declarations and
1385 theorem constants, using only propext, Classical.choice, and Quot.sound.
Outstanding targets type-check, exact verifier output matches, manuscript diff
is empty, and `git diff --check` passes. Self-review checked unitarization and
joint-space reconstruction, continuity and multiplicativity of the resulting
characters, Haar normalization, uniqueness of integer exponents, coefficient
recovery, actual representative-algebra surjectivity, and the two directions
of the Mathieu-predicate equivalence without assuming DvK.


## One-variable DvK source adaptation in progress

The compact abelian/torus correspondence merged in [PR #26](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/26)
at `268eac8b2b4752aae8bc4a2a955739932cdbbedd`, after CI `35194416138` passed.
Current branch: `formalization/one-variable-dvk`.

A fresh external-source search found the MIT-licensed
[MurrellGroup/GMC-2-lean](https://github.com/MurrellGroup/GMC-2-lean/tree/1782de7ff6c97eb1d98e63e7ff34df18b9cd322e)
proof of one-variable DvK. Its source supplies the coefficient extraction
theorem, rather than leaving it as an assumption. The relevant six modules
are being adapted under `MathieuProperty/OneVariableDvK/`, with the original
MIT notice and immutable commit provenance preserved in each file. Gaussian
classification and supporting-face machinery are omitted as unrelated.

The proof extends the zero-adic and infinity valuations to the splitting
field of X^s-zp(X). Partial fractions are expanded in a bilateral summable
series over the zero-adic completion. Vanishing power constant terms forces
the selected root sum to equal z, whereas the infinity valuation proves its
valuation strictly smaller than that of z. This gives a contradiction for
a Laurent polynomial with both negative and positive exponents.

Upstream uses Lean/mathlib 4.29.1; this repository remains pinned to 4.34.0.
The adaptation requires the new bundled monoid-algebra coefficient API,
explicit valuation homomorphisms, and updated topology/typeclass details.
No upstream olean or audit claim is accepted as a substitute for rebuilding
and auditing every adapted declaration locally. The one-variable result
will cover the actual circle Mathieu property; it will not discharge
multivariate DvK or the full torus corollary. All ledger counts remain
unchanged until the relevant proofs build. No manuscript changes.


The six adapted DvK modules and `OneVariableTorus.lean` now build. The
unconditional `one_variable_nonzero_constant_power` applies the proved
coefficient-extraction theorem; no extraction hypothesis survives its signature.
`duistermaat_van_der_kallen_one_variable` proves exclusion of zero from the
literal real convex hull of the integer support. `one_variable_constantTerm_mathieu`
uses strict one-sidedness and the existing support bound to prove eventual
vanishing for every Laurent multiplier. Reindexing the sole exponent and the
actual torus/representative-algebra equivalence yields `torus_one_mathieu`.
A continuous surjective coordinate map yields `circle_mathieu` for the actual
unit-circle group with its Borel structure and normalized Haar integral.

Validation: full `lake build` passed (4016 jobs). Source audit passed for
81 Lean files. The exhaustive namespace audit passed for 1928 declarations
and 1614 theorem constants, with only propext, Classical.choice, and Quot.sound.
The checked-in `scripts/axiom-audit.txt` includes the new core and wrapper
theorems. Outstanding target checks passed, the exact Python verifier output
matched, the manuscript is unchanged from its initial commit, and whitespace
checks passed.

Self-review checked both discrete valuation extensions, the completed field
embedding's injectivity, the annulus fixed-point coefficient argument, the
strict inequality at infinity, and the final unconditional theorem signature.
The wrapper includes the zero-polynomial case, all positive moment exponents,
arbitrary fixed Laurent multipliers, and actual representative Haar integration.
Upstream mathematical content is preserved; changes concern names, targeted
imports, bundled coefficient APIs, explicit valuation homomorphisms, and
topology/typeclass elaboration. Each adapted source retains the MIT license.

Current inventory: 86 PROVED, 13 TODO, 6 IN PROGRESS, 5 BLOCKED (110 total),
with 78 mathematical modules. T04 is now IN PROGRESS because its full
one-variable specialization is proved. The full `thm:dvdk`, `cor:torus`, and
classification remain unproved. A fresh search found no arbitrary-rank Lean
DvK proof; the upstream GMC(2) theorem is explicitly one-variable in its
angular Laurent algebra. The rank-two blocker above is unchanged.


## Direct Zwart counterexamples in progress

The one-variable DvK/circle milestone merged in
[PR #27](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/27)
at `5da9e0a79a9d5cc3a32de4c9f327928ab787dcbe` after CI `35195908666` passed.
Current branch: `formalization/zwart-direct-counterexamples`.

Fresh primary-source inspection suggests a shorter route to E13: directly
refute the specified abelian conjectures using the existing witness, avoiding
their general Euler/KAK implication machinery. The 2025 SU(N) density has a
coordinate with linear weight x. Sp(N) has the same factor in its SU(N)
blocks (rank one has the linear xi weight); G2 has the factor x1. The 2023
SU(N) weight also has a linear coordinate. The 2023 SO(N) density has a flat
coordinate on [-1,1], accessible with the affine version of the earlier xz
witness. These are routes under investigation, not yet marked as proved.

`ZwartLaurent.lean` now compiles locally: its coefficient ring consists of
actual continuous functions on the radial domain, so the spectrum does not
count a formal coefficient that vanishes identically there. It proves the
product-circle Haar/constant-term identity, embeds the univariate polynomial
witness into any chosen torus coordinate, and proves that a product density
x W(y) has zero pure moments while zero belongs to the actual coefficient
spectrum. Admissibility is expressed by membership in the radial coefficient
subalgebra; the intended source subalgebra is generated by the coordinates
and their real square roots sqrt(1-x_i^2). The fixed-source definitions and
weight/domain correspondences remain to be added before E13 can be closed.

Primary sources inspected: Zwart 2023, arXiv:2304.02648 (Definitions 2.9/3.4,
Conjectures 2.10/3.5, SU and SO densities); Zwart 2024, arXiv:2403.02813v1;
Zwart 2025, arXiv:2504.01516v2 (Definition 2.8, Conjectures 2.9/3.1/3.3).
Old SU/Sp/G2 conjectures allow fractional circle exponents on a punctured
circle, so their general integrals cannot simply be defined as constant terms.
Our candidate has integer exponents; its actual angular integral can be
identified with a constant term, but that correspondence must be proved.

The independent Lie-infrastructure check also inspected Yin–Kudryashov,
[Integral Curves and Flows on Banach Manifolds in Lean](https://arxiv.org/html/2602.13247v1),
Section 8. It describes exponential-map/representation correspondence as
future applications. Pinned mathlib has manifold integral curves but no
root-subgroup integration or compact-group highest-weight existence theorem
located. The precise root target remains unchanged.


### Direct SU(N) milestone validation

`ZwartCube.lean` defines the actual radical-polynomial function algebra and
proves its equivalence with the image of multivariate polynomial evaluation.
It proves the product-weight counterexample on the actual finite unit cube.
`ZwartSU.lean` defines the recursive 2025 Jacobian exponent list, verifies both
source dimensions, and proves `sun_conjecture_2025_false` for every SU(N),
N ≥ 2, and every overall normalization constant. The constant coefficient is
nonzero as a function, not just as a formal polynomial. The circle integral is
actual normalized Haar integration, with the constant-term correspondence
proved in `ZwartLaurent.lean`.

Proof substitution: the source implication `sun_reduction_2025` follows from
the proved refutation of its premise. No group parametrization is assumed,
and no theorem-shaped assumption supplies the counterexample. This establishes
the required SU(N) failure directly; it does not assert the general compact Lie
classification. Older fractional-exponent variants and the Sp/G2/SO conjectures
remain open. E13 is consequently IN PROGRESS, not PROVED.

Validation: `lake build` passed (4019 jobs), the source audit passed for 84 Lean
files, and the exhaustive namespace audit checked 2004 project declarations
including 1664 theorem constants. Dependencies are confined to propext,
Classical.choice, and Quot.sound. Outstanding target checks passed; the Python
verifier reproduces the checked-in output exactly; the manuscript remains
unchanged. Self-review checked the recursive exponents, both dimensions,
nonzero functional coefficient, coefficient algebra, all positive powers, and
arbitrary normalization constant. Current inventory: 86 PROVED, 12 TODO,
7 IN PROGRESS, 5 BLOCKED (110 obligations), with 81 mathematical modules.


## Restricted domains and the 2025 G2 conjecture

The SU(N) milestone merged as
[PR #28](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/28)
at `30139441b418b1cff55d2af2204d1e22f95b5a32`, after CI `35197823645`
passed (4m1s). The next branch is `formalization/zwart-restricted-domains`.

`ZwartRestricted.lean` proves that any measurable restriction on the remaining
cube coordinates preserves the linear-coordinate counterexample. It also
proves the Fubini identity converting a cube with a variable final-coordinate
bound into its nested integral. Joint continuity of Laurent evaluation and the
circle/radial Fubini interchange are proved in `ZwartLaurent.lean`.

`ZwartG2.lean` defines the full printed 2025 G2 density, six radial coordinates,
eight circle coordinates, and the bounded last coordinate. Its boundary uses
`sin(arcsin(t)/3)`. The theorem `g2Boundary_sin` verifies the source's preceding
substitution identity on 0 ≤ y ≤ pi/2; the source's complex cube-root expression
is unnecessary for this real boundary. `g2_weightedMoment_nested` proves the
exact order of integration, and `g2_conjecture_2025_nested_false` refutes the
source's assertion with positive powers of the actual Laurent function.
An arbitrary overall constant covers circle/Haar normalizations.

This is a documented direct-proof substitution for contraposition through the
classification. The G2 Lie group and an Euler decomposition are not assumed:
the later corollary asserts failure of this explicitly defined abelian
conjecture, and that failure is proved directly. The unused external implication
to the group's Mathieu conjecture is consequently not load-bearing in this
substitute proof. The full compact Lie classification remains open.

Validation passed: full `lake build` (4021 jobs); source audit (86 Lean files);
exhaustive axiom audit (2035 declarations, 1689 theorem constants; only propext,
Classical.choice, Quot.sound); outstanding target checks; exact Python verifier
comparison; unchanged manuscript; whitespace checks. Self-review compared all
G2 density factors, coordinate indices, coefficient algebra, real boundary,
positive-power range, and nested integration against Zwart 2025 Conjecture 3.3
and the preceding substitution in Zwart 2024. Inventory remains 86 PROVED,
12 TODO, 7 IN PROGRESS, 5 BLOCKED (110 rows), with 83 mathematical modules.

The next Sp(N) route has a locally compiling scratch counterexample for N ≥ 2:
its exponent list concatenates two SU(N) blocks and N linear xi factors;
its region orders xi_1 ≤ ... ≤ xi_N. The explicit block-product correspondence,
rank-one case, and source nested-integral correspondence remain before claiming
that case as covered. Scratch file: `/tmp/ZwartSp.lean`.


## Ordered symplectic domains and the 2025 Sp(N) conjecture

The G2 milestone merged as
[PR #29](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/29)
at `cc4cccc89594629a66c4b03c6f29d42397a8aa87`, after CI `35198695713`
passed (4m5s). Current branch: `formalization/zwart-symplectic-domains`.

`ZwartOrdered.lean` proves that monotone coordinates bounded above form a
measurable set and that integration over this set equals repeated bounded
integrals, including the zero-coordinate base case. It also proves the
measure-preserving block-coordinate equivalence and restricted-cube Fubini
identity. `ZwartSp.lean` applies these to the exact 2025 symplectic conjecture.

The source dimensions N², N(N-1), and N(N+1) are verified. The Jacobian exponent
list is proved to concatenate the two SU(N) blocks with N linear xi factors;
`listWeight_append` gives their product factorization. The pair factor uses the
printed expression in Conjecture 3.1, including its final xi_k exponent. The
refutation does not require modifying that expression. The xi-domain is exactly
0 ≤ xi_1 ≤ ... ≤ xi_N ≤ 1, and `sp_weightedMoment_source` proves the source's
order of x, circle, and nested xi integration. Its positive-power wrapper is
`sp_conjecture_2025_source_false` for N ≥ 2. The separate rank-one theorem
`sp_one_conjecture_2025_false` covers Sp(1), with one linear radial coordinate
and two circle variables. Overall normalization constants are arbitrary.

This completes the three 2025 source conjecture failures by direct proof. The
older 2023/2024 fractional-exponent conjectures and the 2023 SO(N) case remain
open, so E13 and the abelian-reductions corollary remain IN PROGRESS. No general
classification theorem or unproved Lie-group construction is assumed.

Validation: full `lake build` passed (4023 jobs), source audit passed (88 Lean
files), exhaustive namespace audit passed (2101 declarations, 1736 theorem
constants; only propext, Classical.choice, Quot.sound), outstanding target
checks passed, exact verifier output matched, manuscript unchanged, whitespace
checks passed. Self-review checked every index, all three dimensions, both
Jacobian blocks, rank one, repeated bounds, all positive powers, and functional
rather than formal coefficient support. Current inventory: 86 PROVED, 12 TODO,
7 IN PROGRESS, 5 BLOCKED (110 obligations), with 85 mathematical modules.

Next route: extend continuous-coefficient Laurent functions to rational angular
frequencies. Define the actual exponential integral on an angular cube, prove
that embedding integer frequencies reproduces the constant term, and show the
existing witness meets every older bounded-denominator admissibility condition.
The older SU density again has a linear coordinate. Sp/G2 can reuse the ordered
and bounded-domain helpers. For SO use the affine uniform-weight earlier xz
witness; inspect the original PDF's recursive radial indexing carefully before
claiming its source correspondence. General higher-rank DvK and root integration
remain the precise independent blockers recorded above.


## Fractional angular frequencies and the 2024 G2 conjecture

The symplectic milestone merged as
[PR #30](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/30)
at `df8cb0b5646c1dc66bd028b1f4df6c20b2514946`, after CI `35199961725`
passed (5m2s). Current branch: `formalization/zwart-fractional-angles`.

`ZwartFractional.lean` defines continuous-coefficient rational-frequency
Laurent expressions and an actual exponential evaluation on the angular cube.
It proves that integer-frequency embedding preserves moments, coefficient
admissibility, and the Newton polytope. The bounded-denominator condition is
exactly the union of (1/j)Z for 1 ≤ j ≤ D, as in Zwart 2023 Definition 2.9 and
Zwart 2024 Definition 2.10. Positive powers use the proved ring homomorphism;
no constant-term functional is substituted for general fractional integrals.

`ZwartPunctured.lean` proves the unique parametrization of the punctured circle
by angles strictly between zero and 2*pi, constructs the actual functions on
products of punctured circles, and proves their finite rational-power expansion.
The open angular cube has full measure; endpoint removal preserves the actual
integral. The circle-curve derivative and logarithmic Jacobian are proved, so
the parametrized product dz/z integral is exactly (2*pi*i)^M times the angular
moment. The factor is nonzero, and a theorem proves equivalence of zero moments.
Thus the actual fractional integral, coefficient algebra, branch, spectrum of
the specified finite expansion, and normalization are explicit.

`ZwartOldG2.lean` refutes Zwart 2024 Conjecture 3.5 with denominator bound four,
six radial coordinates, eight punctured-circle coordinates, and the source's
bounded radial region and density. The arbitrary constant includes the old
density's factor four. Both nested-angular and parametrized-contour failure
wrappers are proved. This uses the integer witness via the proved embedding;
no G2 Lie-group representation or classification result is assumed.

Validation: `lake build` passed (4026 jobs); source audit passed for 91 Lean
files; exhaustive axiom audit checked 2173 declarations, including 1787 theorem
constants, with only propext, Classical.choice, and Quot.sound; outstanding
target checks passed; Python verifier output matched exactly; manuscript
unchanged; whitespace checks passed. Self-review checked the denominator union,
actual finite expansion, punctured-circle bijection, endpoint null sets,
logarithmic Jacobian, positive powers, and the older G2 source density/domain.
Inventory remains 86 PROVED, 12 TODO, 7 IN PROGRESS, 5 BLOCKED (110 rows), with
88 mathematical modules. E13 remains IN PROGRESS for the 2023 SU/SO and 2024
Sp conjectures.

Next: encode the old SU density using pairs of exponents (a,b) for
x^a*(1-x^2)^b. Its N-th block consists of (1,j-1), j=1,...,N-2, followed by
(2N-3,0), then the SU(N-1) block; the leading pair is (1,0) for every N ≥ 2.
The same linear-coordinate witness and fractional-conjecture implication apply.
The 2024 Sp density uses two of these old SU blocks and the already formalized
ordered xi domain. For SO, verify the original PDF's indexing before encoding;
the intended first coordinate is flat on [-1,1], so use the affine earlier xz
witness. Original PDF text remains `/tmp/mathieu-zwart2023.txt`.

### External SO(N) density indexing discrepancy

Fresh inspection of both arXiv:2304.02648v1 and the published Journal of
Mathematical Physics 64, 101701 (2023), Lemma 3.3, found the same discrepancy:
the stated radial dimension is (N-1)(N-2)/2, but the recursive density uses
j=1,...,n-1 and starts the recursive argument at x_n. At N=3 the domain has
one coordinate, while the formula refers to x_2. The published article was
checked through its full-text reproduction at
https://www.researchgate.net/publication/374458240_On_the_Mathieu_conjecture_for_SU_N_and_SO_N
(the publisher endpoint required a captcha). This is an external-source issue;
no manuscript statement has been changed. The issue was flagged to the user.

The preceding Euler measure, Lemma 3.2, has angular factors sin(phi_j)^(j-1),
j=1,...,N-1, with phi_1 a circle angle and phi_2,...,phi_(N-1) in [0,pi].
After x_(j-1)=cos(phi_j), its well-defined radial block has N-2 variables and
powers (k-1)/2, k=1,...,N-2; the first variable is flat. The recursive argument
would then start at x_(N-1). A generic flat-coordinate counterexample can be
proved independently of the remaining weight, but do not silently identify
that corrected indexing with the printed recurrence or mark its exact source
correspondence PROVED. Investigate an explicit integral-based interpretation
and preserve the distinction in E13/E14.

## Older classical fractional conjectures

PR #31 was squash-merged at `6d3d5af` after CI `35201483662` passed (5m19s).
Current work is on `formalization/zwart-older-classical`.

`ZwartOldSU.lean` encodes the original 2023 SU(N) density by pairs (a,b)
representing x^a (1-x^2)^b, proves the exact radial dimension and its linear
leading factor for all N >= 2, and refutes Conjecture 2.10 with its actual
bounded-denominator algebra and punctured-circle contour integral. The list
weight casts and concatenation formula prove the correspondence to the
recursive source products.

`ZwartOldSp.lean` encodes the 2024 density using two original SU blocks and
N linear xi factors, multiplied by the printed pair factor. In particular,
the final xi_k in the printed pair factor is kept to power one, exactly as
in the source; the direct counterexample does not depend on that factor's
form or on a claimed Haar change of variables. The ordered xi domain and
both source dimensions are those already proved in `ZwartSp.lean`.
Theorems prove equality with the complete paired-list density, the exact
x-then-angle-then-ordered-xi integral order, and its contour normalization.
Conjecture 2.11 is refuted for N >= 2; the N=1 linear-density case is proved
separately. No Sp group decomposition or unproved implication is assumed.

The added finite exponential-sum integration and continuity lemmas justify
Fubini for general rational-frequency expressions, including their powers.
The integer witness is then transferred using the already proved moment,
coefficient-admissibility, and Newton-polytope preservation theorems.

Source review: arXiv:2304.02648, Lemma 2.7 / Definition 2.9 / Conjecture 2.10;
https://arxiv.org/html/2403.02813v1, Definition 2.10 / Conjecture 2.11 and
the displayed density immediately preceding Definition 2.10. The manuscript
is unchanged. E13 remains IN PROGRESS solely for the SO(N) formulation;
E14 still records the distinct external implication/correspondence obligations.

Next: develop a flat-coordinate counterexample on [-1,1] independently of
the SO source's malformed index range, and keep the exact printed recurrence
issue explicit. General DvK and the compact Lie root/quotient bridges remain
open and are not assumed by these direct counterexamples.

Validation: `lake build` passed (4028 jobs); source audit passed for 93 Lean
files; exhaustive axiom audit passed for 2234 project declarations, including
1830 theorem constants, with only propext, Classical.choice, and Quot.sound.
Outstanding target checks passed, exact Python output matched the checked-in
file, manuscript content matched the initial commit, and whitespace checks
passed. Inventory remains 86 PROVED, 12 TODO, 7 IN PROGRESS, 5 BLOCKED out of
110 obligations, with 90 mathematical modules. Self-review checked recursive
weight indices, casted list correspondence, dimensions, N=1, all positive
powers, source integration order, and the nonzero contour normalization.

## Flat radial coordinates and the separate SO Euler family

PR #32 was squash-merged at `12b76a8ca602e2613509491e57334de1690090fe`
after CI `35202982338` passed (4m12s). Current branch:
`formalization/flat-radial-counterexamples`.

`ZwartFlatInterval.lean` proves the affine earlier xz witness has zero pure
moments for actual Lebesgue integration on [-1,1]. Its constant coefficient
is -x after substitution and is nonzero as a function. The product theorem
works for an arbitrary remaining weight and any nonempty remaining domain.
`ZwartSignedCube.lean` specializes this to every finite signed cube, defines
the actual coordinate/square-root polynomial coefficient algebra, proves
its multivariate-polynomial range description, and refutes convex-support
conjectures whenever the first density coordinate is flat. Integer and
bounded-rational frequency versions are both proved.

`ZwartSOEuler.lean` proves the cosine substitution with every continuous
complex test function and every nonnegative integer sine exponent. It
encodes the recursive radial blocks obtained from that substitution,
proves dimension (N-1)(N-2)/2, identifies the square-root powers with the
half-integer real powers, and proves the leading flat factor for every
N >= 3. The resulting separately named `SOEulerConvexSupportConjecture`
is refuted with actual circle integrals. No SO group/Haar parametrization
is assumed or claimed to have been formalized by this module.

**This does not silently correct the printed source.** The named SO Euler
family uses the well-defined angular blocks from source Lemma 3.2. The
malformed recurrence of Lemma 3.3 still has no literal, dimension-correct
interpretation established here. E13 remains IN PROGRESS for that exact
source correspondence; its status is not upgraded by this alternate
family. The manuscript remains unchanged.

Validation: `lake build` passed (4031 jobs); source audit passed for 96 Lean
files; exhaustive axiom audit passed for 2310 declarations / 1886 theorem
constants, with only propext, Classical.choice, and Quot.sound. Outstanding
target checks passed, exact Python output matched, manuscript content was
unchanged, and whitespace checks passed. Self-review checked interval
Lebesgue normalization, the affine factor two, true function coefficient
support, finite products, cosine orientation/endpoints, recursive dimensions,
and the explicit distinction from the source indexing defect. Inventory:
86 PROVED, 12 TODO, 7 IN PROGRESS, 5 BLOCKED / 110; 93 mathematical modules.

Next correspondence check: prove that the rational-frequency expansion is
unique as a function on the angular cube, not just that the specified finite
expansion has the indicated spectrum. Mathlib has multivariate real-analytic
unique continuation (`AnalyticOnNhd.eq_of_eventuallyEq`) and Dedekind character
independence (`linearIndependent_monoidHom`). Extend the finite exponential
sum to R^M, propagate its zero values from the cube interior, then use
character independence. Character-frequency injectivity can be proved by
differentiating a coordinate path at zero. Scratch investigation is in
`/tmp/ZwartUniqueness.lean`; it is not part of the completed milestone.

## Intrinsic rational-frequency spectra

PR #33 merged at `9a2574f77c1379d1ef773c0293f12778cf68ea95` after
CI `35204270261` passed (5m54s). Current branch:
`formalization/rational-spectrum-uniqueness`.

`ZwartUniqueness.lean` proves injectivity of evaluation for every finite
rational-frequency expression on the actual punctured-circle product.
It extends the finite exponential sum to R^M and uses mathlib's multivariate
real-analytic identity theorem to propagate vanishing from the open angular
cube. Dedekind's linear independence of characters then recovers every
coefficient. Distinct frequencies give distinct characters, proved by
differentiating a coordinate path at zero. Equality on the punctured circles
therefore determines the expression, including its continuous coefficient
functions and their support. The proof covers dimension zero and empty
radial domains as well, with no extra hypotheses on them.

`puncturedFunctionHom` gives evaluation as a ring homomorphism;
`puncturedFunctionHom_injective` proves injectivity, and
`puncturedFunctionEquiv` supplies the bijection with its represented-function
range. Thus the spectrum and Newton polytope in the older conjectures are
intrinsic to the function, not an artifact of a chosen finite expansion.
The proof applies to arbitrary rational frequencies, so in particular it
covers every bounded-denominator class and all positive powers.

This is an additional correspondence audit of the existing old SU/Sp/G2
refutations. Their direct proofs replace the external conjecture-to-group
implications; those implications are not assumed by the Lean development.
The exact printed SO density remains unresolved, and E13/E14 retain that
exception. No mathematical manuscript statement has been changed.

Validation: `lake build` passed (4032 jobs); source audit passed for 97 Lean
files; exhaustive axiom audit passed for 2334 declarations, including 1905
theorem constants. Only propext, Classical.choice, and Quot.sound occur.
Outstanding targets type-check, exact verifier output matches, manuscript
content is unchanged, and whitespace checks pass. Self-review checked
analytic continuation from a genuine open set, all finite dimensions,
character injectivity, coefficient recovery, and equality on the punctured
rather than only closed angular domain. Inventory stays 86 PROVED, 12 TODO,
7 IN PROGRESS, 5 BLOCKED / 110, with 94 mathematical modules.

Remaining work requires the substantive unresolved foundations described in
"Detailed obstruction investigation": multivariate DvK (already rank two),
compact-group fundamental representation and root integration, compact Lie
structure and adjoint quotient bridges, and compact abelian Lie group/torus
classification. The algebraic and measure-theoretic downstream transfer
proofs do not supply these existence theorems. No remaining main theorem is
claimed proved, and a successful audit of the current library does not
certify the missing declarations. The independent external SO indexing
exception remains precisely documented above.

## Invariant-form Lie algebra decomposition in progress

PR #34 merged at `72890b8c4c3b7ec2d1aa661794d03145971c3c66` after
CI `35205261216` passed (5m31s). Current branch:
`formalization/invariant-lie-decomposition`.

A fresh library review identified usable machinery in
`Mathlib.Algebra.Lie.InvariantForm`. `InvariantLieDecomposition.lean` now
compiles as a focused algebraic advance toward G01: a symmetric real
bilinear form with no nonzero isotropic vectors and invariant under brackets
gives an orthogonal ideal complement to every ideal. Abelian ideals are
central. The complement of the center has zero center and is semisimple by
mathlib's invariant-form theorem. A bundled Lie algebra equivalence identifies
L with the product of its center and that semisimple ideal.

These are explicit, proved generic algebraic statements. The form hypotheses
are not supplied as substitutes for the missing compact-group theorem. G01
is IN PROGRESS, not PROVED: an invariant positive form must still be constructed
on the actual `GroupLieAlgebra` of a compact Lie group, with bracket invariance
proved. The complete classification and uniform nonabelian theorem remain open.
Inventory changes only from 12 TODO / 7 IN PROGRESS to 11 TODO / 8 IN PROGRESS;
86 PROVED and 5 BLOCKED remain unchanged (110 obligations).

Next route: construct the real adjoint action as the derivative at the identity
of conjugation; prove its homomorphism and continuity properties; average a
positive bilinear form with Haar measure; prove infinitesimal bracket invariance.
`GroupLieAlgebra.lean` supplies invariant vector fields and
`VectorField.mpullback_mlieBracket` provides a possible differential/Lie-bracket
bridge for conjugation diffeomorphisms. Existing project Haar averaging is in
`HaarUnitarization.lean`. These are investigation steps, not claimed results.
All previous DvK/root/source exceptions stay explicit; useful foundational
work is continuing, so the goal is not marked blocked or complete.

Invariant-form milestone validation: `lake build` passed (4039 jobs); source
audit passed for 98 Lean files; exhaustive axiom audit passed for 2353 project
declarations, including 1922 theorem constants. Only propext, Classical.choice,
and Quot.sound occur. Outstanding target checks, exact Python output,
manuscript preservation, and whitespace checks passed. Self-review verified
the explicit anisotropy/invariance hypotheses, ideal orthogonality, centrality
of abelian ideals, trivial center of the complement, semisimplicity, and the
bundled Lie algebra (not just linear) product equivalence. The compact-group
form construction is still unproved, so the ledger remains 86/110 PROVED.
Scratch `/tmp/AdjointLie.lean` has begun the actual conjugation differential;
it is not part of this completed algebraic milestone.

## Actual adjoint action and averaged real form

PR #35 merged at `0afaa36` after CI `35206892844` passed (4m19s).
Current branch: `formalization/compact-adjoint-form`.

`CompactAdjoint.lean` constructs the actual derivative of conjugation at the
identity, proves the representation laws, and proves smoothness using
parameter-dependent manifold differentiation. The fixed source and target
basepoint makes tangent-coordinate changes trivial. Chain-rule calculations
identify the action on left-invariant vector fields; naturality of the
vector-field Lie bracket then proves that each adjoint map is a Lie algebra
automorphism. These are actual group derivatives, not an abstract supplied
adjoint representation.

`HaarRealForm.lean` proves real Haar averaging for arbitrary finite-dimensional
continuous representations, using a Euclidean coordinate model. The resulting
bilinear form is symmetric, positive definite, and invariant under the group.
`CompactAdjoint.exists_positive_adjoint_form` applies this construction to an
actual compact Lie group and derives its topological-group instance from the
Lie-group structure. No invariant form is assumed.

G01 remains IN PROGRESS. The precise remaining bridge is that the differential
at the identity of `g ↦ Ad(g)v`, applied to `x`, equals the actual bracket
`[x,v]`. Differentiating the proved group invariance will then yield
`B [x,v] w = -B v [x,w]`, allowing application of the completed algebraic
decomposition. Preservation of brackets by each Ad(g), now proved, does not
by itself establish this infinitesimal identity. No compact-group decomposition
or main classification is claimed yet. Inventory remains 86 PROVED / 11 TODO /
8 IN PROGRESS / 5 BLOCKED, total 110.

Next: prove the infinitesimal identity using manifold coordinates or a local
left/right-translation calculation. Mathlib's vector-field bracket is
`DW·V - DV·W`; its naturality and all conjugation derivative laws needed above
are now available. No exponential map or root-integration theorem has been
assumed. The manifold and real-form files compile individually; full milestone
validation is pending below.

Adjoint/form milestone validation: full `lake build` passed (4085 jobs).
Source audit passed for 100 Lean files. Exhaustive axiom audit passed for
2437 project declarations / 1993 theorem constants; only propext,
Classical.choice, and Quot.sound occur. Outstanding target statements compile,
the relocated Python verifier reproduces its checked-in output exactly, and
the manuscript is unchanged. Self-review checked the conjugation order,
chain-rule source/target basepoints, smoothness in fixed tangent coordinates,
bracket naturality, positivity at the identity, and right-Haar invariance.
Group invariance is explicitly distinguished from the unproved infinitesimal
bracket invariance. The classification and G01 are not marked proved.

## Infinitesimal adjoint calculation: current work

PR #36 merged at `69fd052` after CI `35208295174` passed (5m13s).
Current branch: `formalization/adjoint-infinitesimal`; no restart or reset.
The merged library has 97 mathematical modules and all recorded audits pass.
Two further mathematical modules are in development, not a finished milestone:
`LieMixedDerivatives.lean` and `LieLocalCoordinates.lean`.

The local proof route avoids constructing a Lie-group exponential map. Write
`c = extChartAt I 1`, `a₀ = c 1`, and
`μ(a,b) = c(c.symm a * c.symm b)` near `(a₀,a₀)`. Let
`L_v(a) = Dμ(a,a₀)(0,v)` and `R_v(a) = Dμ(a₀,a)(v,0)`.
Symmetry of the second derivative proves `D L_v(a₀)x = D R_x(a₀)v`.
The generic calculus lemma `LieMixed.adjoint_derivative` is proved: differentiating
`R(a) A(a) v = L(a) v`, with the identity first derivatives at `a₀`, gives
`D A(a₀)x v = D L_v(a₀)x - D L_x(a₀)v`.

The actual coordinate multiplication is smooth, its left/right identity laws
hold on the chart target, both first partial derivatives at the identity are
identities, and the coordinate adjoint map `a ↦ Ad(c.symm a)` is smooth and equals
the identity at `a₀`. These proofs compile in scratch and have been preserved in
the two new modules. Remaining work: identify `L_v` with the chart pullback of
the actual left-invariant vector field; prove `R(a)Ad(c.symm a)=L(a)` using
`R_g ∘ conjugation_g = L_g`; identify the resulting difference of derivatives
with `GroupLieAlgebra.bracket_def`. Finally differentiate the already proved
adjoint invariance of the positive bilinear form. Neither the infinitesimal
identity nor bracket invariance is claimed proved yet, so G01 remains IN PROGRESS.

Useful library facts found: `mfderiv_extChartAt_self` and
`mfderivWithin_range_extChartAt_symm` identify the chart derivatives at the
basepoint with identity maps; `ContDiffAt.isSymmSndFDerivAt` handles mixed
partial symmetry. For `I = 𝓘(ℝ,E)`, its range is univ, so inverse-chart within
statements become unrestricted ones. Scratch snapshots: `/tmp/LieMixed.lean`
and `/tmp/LieLocalChart.lean`; logs `/tmp/mathieu-lie-mixed.log` and
`/tmp/mathieu-lie-chart.log`. All actual mathematical source files belong in
`MathieuProperty/`; tooling remains in `scripts/`.

## G01 completed: compact Lie algebra decomposition

The local-coordinate route succeeded. `LieLocalChart.adjointCoordinates_fderiv`
proves the actual infinitesimal adjoint/Lie-bracket identity. The proof uses the
chain rule for left/right translations, symmetry of mixed derivatives, and the
exact chart pullbacks of the actual invariant vector fields. No exponential
map, integration theorem, or supplied adjoint representation is assumed.
Differentiating Haar-averaged adjoint invariance then proves
`CompactAdjoint.invariantForm_lieInvariant`.

`CompactAdjoint.compact_lie_decomposition` now constructs the center complement,
a bundled Lie algebra product equivalence, and finitely many independent simple
factors spanning the complement. `liftCentralIdealEquiv` embeds those factors
as actual ideals of the full Lie algebra; `simple_factor_positive_form` supplies
the inherited symmetric positive invariant forms. This covers every assertion
of manuscript equation `eq:compact-lie-algebra-decomposition`, including compact
type and the zero-factor case. The separate claim that nonabelian connected G
has at least one factor remains G02 and is not assumed or marked proved.

G01 moves IN PROGRESS → PROVED. Inventory is now 87 PROVED / 11 TODO /
7 IN PROGRESS / 5 BLOCKED = 110. There are 100 mathematical modules plus the
umbrella, and 103 project-owned Lean files including the audit helpers.
The general DvK, highest-weight/root integration, central covers, actual adjoint
simple quotient, uniform nonabelian theorem, and main classification remain
open. The mathematical manuscript is unchanged.

The complete factor-embedding and compact-type refinement passed full
`lake build` (4089 jobs) and the audits recorded below. Next substantive task is G02: prove
that a connected Lie group with abelian Lie algebra is abelian, then extract a
simple factor for every nonabelian connected compact group. A fresh search
found no direct manifold theorem asserting that a map with zero differential
is locally constant; investigate chart-local mean-value arguments and existing
connected/locally constant APIs. G03 is preservation of the finite simple-factor
family under the now-proved continuous adjoint action.

G01 milestone validation completed: full `lake build` passed (4089 jobs), source
audit passed (103 Lean files), and exhaustive axiom audit passed (2534 project
declarations / 2066 theorem constants). Only propext, Classical.choice, and
Quot.sound occur. The outstanding-target checks compile, exact Python verifier
output matches byte for byte, manuscript preservation and whitespace checks
pass. Correspondence review checked the center as an actual ideal, the natural
addition Lie equivalence, finite independent simple factors spanning the
complement, their ambient ideal embeddings, inherited positive invariant forms,
and the possibility of zero simple factors. G02's nonabelian/nonzero-factor
claim and G03–G06's quotient/connectedness assertions are not included or assumed.

## G02: connectedness and zero differentials

PR #37 merged at `65ce93f` after CI `35210769133` passed (5m9s).
Current branch: `formalization/connected-lie-abelian`. G01 is completed and
merged. G02 now compiles in full; inventory is 88 PROVED / 10 TODO /
7 IN PROGRESS / 5 BLOCKED = 110.

Four new mathematical modules implement the connectedness step:

- `ManifoldZeroDerivative`: a chart-local mean-value proof that locally zero
  differential implies local constancy, including manifold-valued maps.
  `eq_of_mfderiv_zero` gives constancy on a preconnected real manifold.
- `LieHomCalculus`: a smooth translation identity propagates zero differential
  at the identity to all points. `hom_eq_of_mfderiv_eq` proves uniqueness of
  smooth homomorphisms on a connected real Lie group from their differentials.
  For f,h use δ(g)=f(g)h(g)⁻¹; differentiate δ(g)h(g)=f(g) at 1 and then use
  δ(kg)=f(k)δ(g)h(k)⁻¹ to propagate the zero differential.
- `ConnectedLie`: the local-coordinate infinitesimal-adjoint theorem becomes
  `adjoint_mfderiv`, the actual manifold differential at 1. If the Lie algebra
  is abelian, Ad has zero differential and is constant. Comparing conjugation
  with the identity homomorphism then proves `mul_comm_of_lie_abelian`.
- `NonabelianCompactLie`: nonabelianity forces the center complement from G01
  to be nonzero. Since its atomic simple ideals span it, at least one exists.
  Transporting simplicity through the already-proved ambient ideal embedding
  gives `CompactAdjoint.nonabelian_simple_ideal` with no group/Lie-algebra
  correspondence assumed as a hypothesis.

This is a documented elementary differential-calculus substitute for invoking
Lie exponential/integration theory for G02. The generic connected-group bridge
requires a complete real chart model, automatically available for the final
finite-dimensional compact-group theorem. Neither compactness nor finite
dimension is added to the generic zero-differential or homomorphism results.
The final wrapper derives the topological-group structure from the Lie-group
structure. The Borel measurable structure is the existing normalized-Haar model.

Next: G03, showing the connected adjoint action preserves each simple ideal.
A promising route is the finite independent atomic-factor family from G01:
Lie automorphisms permute the simple factors, finite-dimensional ideals are
closed, and connectedness forces the finite orbit to be constant. G04–G06
still require constructing the adjoint simple quotient as a Lie group, not
merely an abstract continuous representation. General DvK and root integration
remain open. No conditional main theorem or manuscript change has been made.

Milestone validation: full `lake build` passed (4093 jobs); the source audit
passed for 107 Lean files; exhaustive axiom audit passed for 2587 project
declarations / 2106 theorem constants, with only propext, Classical.choice,
and Quot.sound. Outstanding-obligation statement checks compile, the exact
Python verifier matches its checked-in output byte for byte, and manuscript
preservation and whitespace checks pass. The source correspondence review
checked the full nonabelian/compact/connected hypotheses, the actual
GroupLieAlgebra bracket, and that the resulting simple object is an ambient
Lie ideal rather than just an abstract Lie algebra. No quotient-group claim
is included in G02. All auxiliary tooling and associated outputs stay under
`scripts/`; mathematical modules stay in `MathieuProperty/`.


## G03: connected adjoint action on the simple factors

PR #38 merged at `4f6cad1` after CI `35212577456` passed (5m51s).
Current branch: `formalization/adjoint-simple-ideals`. G03 compiles in full;
inventory is 89 PROVED / 9 TODO / 7 IN PROGRESS / 5 BLOCKED = 110.

`LieIdealOrbit.idealOrderIso` transports ideals along an actual Lie equivalence.
The generic `atom_image_eq` theorem proves that a continuous family of real
finite-dimensional Lie automorphisms on a preconnected parameter space acts
constantly on the atomic ideals whenever that ideal family is finite. Each
fiber is closed: membership in an image atom is characterized by all its
vectors lying in the target atom, and finite-dimensional subspaces are closed.
A map to a finite discrete set with closed fibers is continuous and therefore
constant on a connected space.

`AdjointIdeals` first proves that Ad preserves the center's orthogonal
complement using its Haar-averaged invariant form. Restriction gives the actual
Lie automorphisms `semisimpleAdjointEquiv`. The finite-family theorem then gives
`adjoint_preserves_atom`; lifting the factor to the ambient Lie algebra yields
`adjoint_preserves_simple_ideal`, exactly the factors used in the manuscript's
decomposition. `simpleAdjointRepresentation` and its continuity theorem give
the restricted representation on each such ambient simple ideal.

The next obligations are G04–G06. The remaining quotient target needs an actual
Lie group structure on the inner automorphism group. A search of the pinned
manifold library found no closed-subgroup/Lie-subgroup theorem. For G06, a
possible direct substitute is surjectivity of a smooth homomorphism onto a
connected Lie group when its differential at 1 is surjective: mathlib's
`HasStrictFDerivAt.map_nhds_eq_of_surj` supplies the normed-space local openness
step; charts should transfer it to manifolds, and an open subgroup of a
connected group is the whole group. This would avoid assuming a closed
subgroup theorem for the final surjectivity step. G04 itself remains open.

Milestone validation: full `lake build` passed (4095 jobs); source audit passed
for 109 Lean files; exhaustive axiom audit passed for 2664 project declarations
and 2172 theorem constants, using only propext, Classical.choice, and Quot.sound.
The outstanding-obligation checks compile, exact verifier output matches,
manuscript preservation and whitespace checks pass. An umbrella-import name
collision between automatically named local instances was fixed by assigning
explicit names to this module's local instances; no mathematical change was
needed. Correspondence review checked the actual Ad action, center-complement
invariance, finite atomic factors, ambient ideal lifting, and continuity of the
restricted representation. G04–G06 and the quotient proposition remain open.
The manuscript, verifier mathematics, and existing proofs remain unchanged.


## G05–G06: restricted differential and surjectivity

PR #39 merged at `a61f02b` after CI `35213398864` passed (5m54s).
Current branch: `formalization/restricted-adjoint-differential`.
G05 and G06 now compile in full. Inventory: 91 PROVED / 7 TODO /
7 IN PROGRESS / 5 BLOCKED = 110.

`LieSurjective` proves `range_mem_nhds_of_surjective_mfderiv` for real Banach
manifold charts. It uses `contMDiffAt_iff` to work in the preferred charts and
mathlib's strict derivative/open-mapping theorem. The image contains a
neighborhood of the image point. For a homomorphism, the image subgroup is
then open and closed, hence all of a connected target.
`surjective_of_surjective_mfderiv` needs only C¹ regularity at the identity
and a surjective differential. This substitutes for the manuscript's
closed-connected-subgroup argument at G06. It applies to the actual map once
G04 supplies its target Lie group; it does not construct or assume that target.

`RestrictedAdjointAlgebra` proves `exists_restricted_adjoint` and
`restricted_adjoint_range`: an ideal's invariant orthogonal complement is an
ideal and commutes with it, so every restricted ambient adjoint operator is
ad(z) for some z in the ideal. The converse inclusion is immediate.

`ProjectedAdjoint` expresses restriction as a continuous linear map on
endomorphisms, using a projection p onto a subspace. Composition proves
smoothness. The actual manifold chain rule and the already-proved
infinitesimal Ad theorem give D(projected Ad)(1)(x)(v)=p([x,v]).

`RestrictedAdjoint` constructs p from the invariant orthogonal ideal complement.
`restrictedAdjoint_mfderiv` identifies the derivative with the actual restricted
bracket. `restricted_adjoint_differential_range` identifies its image with
{ad(z) | z lies in the ideal}; `restrictedBracket_self` records the exact
identification with mathlib's `LieAlgebra.ad`. For every simple factor,
`restrictedAdjoint_eq_simple` identifies the constructed map with G03's actual
`simpleAdjointRepresentation`, using the proved Ad-invariance. Thus neither
a projection nor the differential formula is assumed. The derivative is
computed in the ambient finite-dimensional endomorphism space, as in the
manuscript's matrix realization of the automorphism group.

G04 is now the remaining structural obligation in this portion of the quotient
proof. It requires constructing the inner-automorphism group as an actual
compact connected adjoint simple Lie group and identifying its Lie algebra
with ad of the simple ideal. No such Lie-group target has been assumed.
A search found manifold immersion/submersion and implicit-function modules,
but no ready-made closed-subgroup or constant-rank image theorem. Possible
next routes are a specialized Lie structure on the compact restricted-Ad
image (constant rank), or a local construction of the automorphism group
using its derivation algebra and matrix exponential. The root-subgroup and
general DvK gaps are still separate outstanding obligations.

Milestone validation: full `lake build` passed (4099 jobs), source audit
passed for 113 Lean files, and exhaustive axiom audit passed for 2751 project
declarations / 2246 theorem constants. Only propext, Classical.choice, and
Quot.sound occur. Outstanding-obligation checks compile; the exact verifier
matches byte for byte; manuscript preservation and whitespace checks pass.
Correspondence review checked the actual restricted representation identity,
the derivative sign and base point, the precise ad-image equality, and the
surjectivity theorem's C¹ and connected-target hypotheses. The quotient Lie
group itself is not claimed. The manuscript and exact verifier remain
unchanged; auxiliary tooling remains under `scripts/`.

Further G04 search: the pinned `Submersion.lean` explicitly lists the implication
from surjective differential to submersion as future work, and there is no
constant-rank image construction ready to use. Mathlib does prove all
derivations of a finite-dimensional Killing Lie algebra are inner in
`Algebra/Lie/Derivation/Killing.lean`. Its exponential-of-derivation API only
covers nilpotent derivations, so a general analytic exponential/automorphism
bridge would need development. Another useful intermediate target is the
actual compact connected image of the restricted representation inside units
of continuous endomorphisms, with a proof that its center is trivial; that
would isolate the remaining manifold/Lie-algebra identification problem.


## G04: concrete compact adjoint image

PR #40 merged at `c92c0b6` after CI `35214838310` passed (6m30s).
Current branch: `formalization/adjoint-image-topology`.
Inventory: 91 PROVED / 6 TODO / 8 IN PROGRESS / 5 BLOCKED = 110.
The previous complete build passed 4099 jobs; exhaustive audit was 2751
project declarations / 2246 theorem constants.

`RepresentationImage` constructs a homomorphism into units of continuous
endomorphisms from a finite-dimensional representation. It proves continuity,
constructs the range subgroup and continuous surjection onto it, and proves
compactness and connectedness from those of the source. This is a concrete
topological group construction, not a claimed Lie-group structure.

`AdjointImage` applies this to the actual simple-factor representation from
G03/G05. It constructs `simpleAdjointImage` and `simpleAdjointOnto`, proving
compactness, connectedness, continuity, and surjectivity. Every image element
preserves the Lie bracket, via `simpleAdjointImage_map_lie`, and thus gives an
actual Lie automorphism `simpleImageLieEquiv` of the factor.

`AdjointCentralizer.commutes_mfderiv` differentiates a constant operator's
commutation with a smooth family. `equiv_eq_refl` shows a Lie automorphism of a
centerless Lie algebra that commutes with all adjoint operators is identity.
For a central image element, G05's actual derivative identifies the resulting
commutation with all ad(x). The simple factor has zero Lie center, so the image
element is identity. This proves `simpleAdjointImage_center_eq_bot`.
`simpleAdjointImage_nontrivial` rules out a trivial image: that would make the
restricted representation constant and its differential zero, contrary to the
nonabelian simple factor's bracket.

This is a nontrivial compact connected centerless **topological** quotient.
G04 remains IN PROGRESS: it has no manifold charts or Lie-algebra identification
yet, and no claim of a compact adjoint simple **Lie** quotient is made.
The current draft is `/tmp/AdjointImageNext.lean`, now split into the repository
modules. Full milestone validation passed: `lake build` completed 4102 jobs;
source audit passed for 116 Lean files; exhaustive axiom audit passed for
2818 project declarations / 2296 theorem constants, using only propext,
Classical.choice, and Quot.sound. Outstanding-obligation checks compile;
the verifier matches byte for byte; manuscript preservation and whitespace
checks pass. Correspondence review checked the concrete unit-group image,
actual restricted Ad coefficients, full continuity/surjectivity, Lie-bracket
preservation, centerlessness, and nontriviality. It explicitly excludes the
unconstructed Lie-group structure from the proved scope.

Next G04 route to investigate: build local charts on the automorphism group of
a finite-dimensional real Killing Lie algebra. Mathlib proves every derivation
is inner (`LieDerivation.IsKilling.exists_eq_ad`). For the analytic bridge,
prove the exponential of a continuous derivation preserves the bracket. A
specialized route is to differentiate
exp(-tD)([exp(tD)x, exp(tD)y]); the derivation rule makes its derivative zero,
so it equals [x,y]. Prove this first for any continuous bilinear operation B
and continuous linear D satisfying D(Bxy)=B(Dx)y+Bx(Dy), avoiding unnecessary
normed-Lie typeclass machinery. The finite-dimensional Lie bracket then has a
continuous bilinear model via `LinearMap.toContinuousBilinearMap`.
The existing exponential derivative theorem is
`NormedSpace.hasDerivAt_exp_smul_const` (and its primed variant).

With exponential automorphisms and inner derivations, use the inverse function
theorem on a map combining coordinates along ad(L) with the independent
bracket-preservation equations. This may construct the local automorphism
chart without a general closed-subgroup theorem. An alternative is a
constant-rank construction for the compact representation image; the pinned
library has no ready-made constant-rank image theorem. Neither route has been
assumed. All manuscript and exact-verifier content remains unchanged.


## G04 automorphism local charts — current milestone

The next analytic bridge is now formalized, independently of Lie-bracket
normed-space instances. For every continuous bilinear operation B on a real
Banach space, `DerivationExponential.exp_preserves_bilinear` proves that the
exponential of a bounded derivation preserves B. The proof differentiates
exp(-tD)(B(exp(tD)x, exp(tD)y)) and uses the zero-derivative constancy theorem.
`BilinearAutomorphism.group` is the actual closed subgroup of units in the
continuous endomorphism algebra preserving B; `exp_mem_group` puts derivation
exponentials in that subgroup.

`BilinearDefect` defines the smooth equations F(T)(x,y)=T(B(x,y))-B(Tx,Ty).
`linearDefect_apply` computes their derivative at identity, and
`mem_derivations_iff` identifies its kernel exactly with the derivation rule.
`FiniteDimensionalSlice` projects the equations to the derivative image and
uses Mathlib's implicit function theorem to produce ambient local coordinates
with derivative-image and derivative-kernel components.

For finite-dimensional V, `AutomorphismParametrization` applies a second inverse
function theorem to the projection of exp(D)-1 along the derivation subspace.
`exponential_logarithm_eventually` proves that every sufficiently small solution
of the projected equations equals the exponential of the constructed logarithm.
Consequently `defect_zero_iff_projected_eventually` proves that projected and
full bracket-preservation equations have identical local zero sets. This is a
proved local equivalence, not an assumption of constant rank.

`AutomorphismChart.exists_identity_chart` now gives an actual
`OpenPartialHomeomorph (group B) (derivations B)` whose source contains identity,
whose forward map is the ambient local logarithm, and whose inverse is the
actual unit-group exponential. `logarithm_smoothAt_one` proves ambient smoothness
at identity; `exponential_smooth` is global. `LocalInverseChart` packages the
continuous local-inverse argument. Full validation passed: `lake build` completed
4114 jobs; source audit checked 123 Lean files; exhaustive axiom audit checked
2972 project declarations / 2434 theorem constants, with only propext,
Classical.choice, and Quot.sound. Both minimal-obligation checks compile, the
verifier matches byte for byte, and manuscript preservation and whitespace checks
pass. Correspondence review confirmed the actual unit-group topology, local
chart source at identity, exact exponential inverse, and absence of assumed
constant-rank or closed-subgroup results.

G04 remains IN PROGRESS. The next steps are to shrink to a smooth chart domain,
translate this chart to a smooth atlas, prove the actual automorphism group is
a Lie group, identify its Lie algebra with the derivation algebra, and apply
innerness of derivations of the simple factor. No Lie-group instance, actual
simple Lie quotient, or final classification has been claimed yet. The
manuscript and exact-verifier mathematical content remain unchanged.


Resume note: for a uniformly smooth chart domain, use the analyticity of the
polynomial defect and operator exponential. Strengthen the helper smoothness
proofs to `ContDiff ℝ ω` (or add analytic variants), then apply
`ContDiffAt.contDiffOn` with target order infinity; a mere `ContDiffAt ℝ ∞`
statement does not by itself supply one common smooth neighborhood in this API.
Shrink the identity chart to that neighborhood before translating it.


## G04 actual automorphism Lie group — current milestone

PR #42 merged as `176fc92`, with CI passing in 5m29s. The next local draft
`/tmp/AutomorphismAnalyticNext.lean` has now compiled and is split into
`AutomorphismManifold` and `AutomorphismLieGroup`.

`logarithm_analyticAt_one` strengthens the local logarithm regularity to real
analyticity. `exists_analytic_identity_chart` shrinks the actual chart source
to a domain where this ambient logarithm is analytic at every point.
`translatedChart` translates by group multiplication; these charts define the
actual subtype topology's `ChartedSpace`. Their transition maps are the ambient
logarithm composed with fixed matrix multiplication and exponential. Their
analyticity proves `IsManifold` at order omega.

The matrix embedding is analytically smooth (`val_contMDiff`), and
`contMDiffAt_of_val` proves smoothness into the group from continuity and
smoothness of the actual matrix coefficients. Multiplication is matrix
composition; inversion uses the existing Lie-group structure on units of the
complete endomorphism algebra. This proves the actual `LieGroup` instance at
order omega, hence also infinity. `val_mfderiv_one` identifies the differential
of the matrix embedding with inclusion of the derivation subspace.

Full validation passed: `lake build` completed 4117 jobs; source audit checked
125 Lean files; exhaustive axiom audit checked 3013 project declarations /
2472 theorem constants, using only the permitted standard foundations.
Outstanding-obligation checks compile, exact verifier output matches, and the
manuscript and whitespace checks pass. Correspondence review checked the
original subgroup topology, analytic chart domains, transition maps, matrix
embedding, actual multiplication/inversion, and embedding differential.

G04 remains IN PROGRESS: the tangent
Lie bracket still needs identification with the derivation commutator, then
innerness of derivations and the compact adjoint-image/identity-component
correspondence. No compact simple Lie quotient or classification is claimed.
The next useful route is to compute the local logarithm derivative, express
actual group Ad as projected matrix conjugation, and differentiate at identity
using the already proved `ConnectedLie.adjoint_mfderiv`. This avoids assuming
any general Lie-homomorphism differentiation theorem absent from the library.


## G04 tangent Lie bracket — work in progress

PR #43 merged as `86066d1`, with CI passing in 5m43s. Current branch is
`formalization/automorphism-lie-algebra`. Two new modules have passed focused
builds but are not yet in the umbrella or a validated milestone.

`AutomorphismDifferential.logarithm_hasFDerivAt_one` computes the local logarithm
derivative as projection onto derivations. `adjoint_eq_projection` computes the
actual group adjoint action in these charts. Conjugating a derivation by an
automorphism is proved to remain a derivation (`conjugationOperator_mem`), so
`adjoint_val` removes the projection and identifies the actual Ad with matrix
conjugation. Differentiating exp(X)Yexp(-X) at zero gives XY-YX.

`AutomorphismBracket.tangentVal_lie` now identifies the actual tangent Lie
bracket with the operator commutator, by evaluating the differential of actual
Ad and applying the previously proved `ConnectedLie.adjoint_mfderiv`. It uses a
local 800000-heartbeat limit for this composite proof; no proof mechanism or
axiom is changed. Focused build passed (10 seconds).

The current next draft is `/tmp/LieAutomorphismNext.lean`: specialize the
bilinear operation to a finite-dimensional real Lie bracket and identify the
tangent algebra with Mathlib's `LieDerivation`. The normed and Lie structures
must share their additive/module data. Independent `[NormedAddCommGroup V]`
and `[LieRing V]` parameters caused an instance diamond, so the draft uses an
explicit `NormedRealLieAlgebra` structure merging these standard data, without
any bracket norm bound or structural theorem. It must be instantiated from the
actual simple ideal before this route can close G04. The next mathematical
steps are the Lie equivalence to derivations, Mathlib's inner-derivation theorem
for Killing algebras, and identification of the compact image with the relevant
identity component. All such obligations remain open in the coverage ledger.


The norm compatibility layer is now constructed and compiled in
`NormedLieModel`: `groupLieAlgebraNormed` copies the actual chart-model norm
onto the group Lie algebra, and `idealNormedRealLieAlgebra` restricts it to
ideals. The complete-space requirement of the group Lie bracket is available
for the finite-dimensional models used here. This adds no structural hypothesis.

`LieAutomorphism.tangentLieEquiv` now identifies the actual automorphism-group
Lie algebra with Mathlib's `LieDerivation`. Its inverse sends a derivation to
its continuous finite-dimensional endomorphism. Bracket preservation uses the
new actual commutator theorem. `innerDerivationEquiv` uses Mathlib's proved
surjectivity of ad for Killing algebras and injectivity from trivial center.
`algebraEquiv` identifies the actual automorphism-group Lie algebra with the
original Killing algebra. Cartan's criterion supplies the Killing hypothesis
for a finite-dimensional real simple algebra, proving `algebra_isSimple`.

The smoothness criterion `contMDiffAt_of_val` is generalized to arbitrary order
n, since the original source compact Lie group is smooth at order infinity,
while the matrix automorphism target has the stronger analytic structure.
The proof uses the already analytic logarithm at the requested order.

Four new modules are now in the umbrella. Full validation passed: `lake build`
completed 4138 jobs; source audit checked 129 Lean files; exhaustive axiom audit
checked 3121 project declarations / 2546 theorem constants, with only the
permitted standard foundations. Outstanding-obligation checks compile; the
verifier is byte-identical; manuscript preservation and whitespace checks pass.
Correspondence review checked the actual group bracket, exact derivation
equivalence, use of Mathlib innerness/Cartan criteria, and construction of the
norm compatibility layer from actual group Lie algebras and ideals.
The next step is to codomain-restrict the actual simple-factor representation
to this automorphism group, use G05 and inner derivations to prove its
differential surjective, and obtain an open compact connected image. An open
subgroup inherits charts from the ambient group (the pinned library has
manifold instances for `TopologicalSpace.Opens`, but no ready-made
`OpenSubgroup` Lie-group instance was found). Its Lie algebra must then be
identified with the already simple ambient algebra. G04 stays IN PROGRESS.

## Automorphism Lie-algebra milestone merged; next image bridge

PR #44 was squash-merged at `2d698a6` after CI run `35221839448` passed.
The next branch is `formalization/adjoint-open-image`. Standalone Lean drafts
prove smoothness of the actual restricted adjoint homomorphism into the
automorphism Lie group and surjectivity of its differential. A second draft
constructs the inherited Lie-group structure on open subgroups. These drafts
are not yet integrated into the library or counted as completed G04 coverage.
The remaining steps are openness and identity-component correspondence, then
the actual image Lie-algebra identification and manuscript-facing quotient
theorem. Inventory remains 91 PROVED / 6 TODO / 8 IN PROGRESS / 5 BLOCKED,
110 obligations total.

## Adjoint simple quotient — current milestone

Three new modules close G04 and `prop:adjoint-simple-quotient`. The coverage
inventory is now 93 PROVED / 5 TODO / 7 IN PROGRESS / 5 BLOCKED = 110.
There are 129 mathematical modules plus the import umbrella.

`AdjointAutomorphism` codomain-restricts the actual restricted adjoint action
to the constructed automorphism Lie group. The matrix embedding differential
identifies its derivative with the already checked restricted bracket. Every
derivation of the simple ideal is inner, so this differential is surjective.
Local openness gives an open image subgroup; connectedness and clopenness
identify it exactly with the automorphism identity component.

`OpenLieSubgroup` restricts ambient charts to any open subgroup. Multiplication
and inverse are smooth in these charts. Inclusion has identity differential
on the common model. The conjugation chain rule therefore identifies adjoint
operators, and a second derivative identifies the actual group Lie brackets.
The resulting `lieEquiv` uses the actual Mathlib group Lie algebras.

`AdjointQuotient` gives the concrete image its compact connected Lie-group
structure, constructs the continuous smooth surjective quotient map, and
identifies its Lie algebra with the simple factor. Forgetting the redundant
automorphism membership proof gives a multiplicative equivalence with the
earlier matrix image; its proved centerlessness transfers to the new target.
`CompactAdjoint.adjoint_simple_quotient` selects an actual simple factor from
nonabelianness and proves the manuscript proposition with no existence input
for the quotient. The target is explicitly the automorphism identity component,
as required for the adjoint form.

Material proof substitution: local openness from the surjective differential
replaces the manuscript's closed-connected-subgroup argument. The conclusion
and hypotheses are preserved. The Borel and topological-group structures in
the implementation are the existing structures used throughout the Haar
construction, rather than additional mathematical existence assumptions.

General multivariate DvK remains deferred as directed. The general simple-group
witness and uniform nonabelian theorem still await the separately documented
representation/root-integration and covering prerequisites. Closing the adjoint
quotient does not close those downstream statements.

Validation passed: `lake build` completed 4141 jobs; the source audit checked
132 Lean files; the exhaustive axiom audit checked 3233 project declarations /
2639 theorem constants, using only `propext`, `Classical.choice`, and `Quot.sound`.
The manuscript-facing quotient theorem is included explicitly in the printed
axiom reports. The outstanding targets type-check, the verifier reproduces the
checked-in output byte for byte, the manuscript is unchanged from its initial
commit, and whitespace checks pass. Correspondence review checked the actual
quotient map, open image topology, inherited group bracket, simple-factor
identification, identity-component equality, and center transport.

## Abelian-group route: one-parameter subgroups

PR #45 merged at `7537bd4` after CI `35224127353` passed (7m27s).
The next branch is `formalization/abelian-one-parameter`. A targeted search found
usable manifold integral-curve existence, uniqueness, and uniform-time extension
theorems in pinned Mathlib. This supports a direct route toward T01 without
assuming a general Lie exponential or faithful representation theorem.

The standalone `LieOneParameter` draft compiles: translation of a local integral
curve of the actual left-invariant field gives a uniform interval at every point;
Mathlib extends it globally. Uniqueness supplies the homomorphism law. The curve
is continuous, is C¹ in manifold charts, and has the prescribed tangent vector
at zero. This works for Hausdorff real Lie groups with complete model space.
The module is now being integrated; full milestone validation remains pending.

Next: for an abelian group, multiply the finitely many one-parameter subgroups
associated with a tangent-space basis. The derivative should be an isomorphism,
giving an open surjection from a real vector group. The kernel must then be
proved discrete and, using compactness, a full lattice. Mathlib's `ZLattice`
basis machinery is available for the final lattice step. None of this yet
proves T01; its coverage status is retained until the bridge is verified.
General DvK remains deferred; root integration and highest-weight existence
are not being assumed by this construction.

The basis-product construction now compiles as well: `parameterMap` is a C¹
homomorphism from the real coordinate vector group. Its differential at zero
is exactly the inverse basis-coordinate equivalence, hence bijective. For a
connected abelian target, the proved local-openness theorem makes the map
surjective. T01 is now IN PROGRESS: 93 PROVED / 4 TODO / 8 IN PROGRESS /
5 BLOCKED, total 110. The kernel and lattice steps remain unproved.

`AbelianLattice` now compiles as a standalone draft. The inverse function theorem
in the actual chart isolates zero in the kernel, proving its discreteness.
The continuous vector-group surjection is open by Mathlib's sigma-compact
group open mapping theorem. If the kernel had proper real span, a nonzero
linear functional annihilating it would descend continuously to the compact
target and surject onto ℝ, a contradiction. Thus the actual kernel is a full
`IsZLattice`. The finite product-of-circles equivalence remains to be constructed;
T01 is not yet marked PROVED.

## Compact abelian Lie groups are tori — current milestone

Five new mathematical modules close T01. The inventory is now 94 PROVED /
4 TODO / 7 IN PROGRESS / 5 BLOCKED = 110; there are 134 mathematical modules.
This proves the group-theoretic identification with a torus, not the torus
Mathieu theorem or the main classification. The latter still require general
DvK, which remains deferred as instructed.

`LieOneParameter` constructs global C¹ one-parameter subgroups for every tangent
vector using Mathlib's manifold ODE existence, uniqueness, and uniform-time
extension. Left translation gives the same local existence interval at every
point; no global Lie exponential or integration theorem is postulated.
`AbelianParameters` multiplies the subgroups for a finite tangent basis. Its
differential is the inverse basis-coordinate map, so the homomorphism is onto
a connected abelian group by the already proved local-openness argument.

`AbelianLattice` uses the inverse function theorem to isolate zero in the
kernel. The kernel is discrete. The open mapping theorem lets a real linear
functional annihilating the kernel descend continuously to the compact group.
A nonzero such functional would surject onto ℝ, which is not compact. Hence
the kernel spans the real vector space and is a full integer lattice.

`LatticeTorus` sends coordinates in a lattice basis through `AddCircle 1` to
the complex unit circle. Its kernel is exactly the given lattice and the map
is continuous and surjective. `AbelianTorus` compares the two actual quotient
maps with equal kernels. The induced multiplicative equivalence is continuous
by the quotient-map criterion, and its inverse is continuous by compactness
and Hausdorffness. `CompactLieTorus.exists_torus_equiv` gives the torus of
dimension `finrank ℝ E`. `CompactLieTorus.abelian_iff_torus` is the manuscript-facing
iff, with the actual group operations and topology. The proof covers an empty
basis, so dimension zero is included.

This substitutes an explicit one-parameter/lattice construction for a packaged
compact abelian Lie-group classification theorem absent from pinned Mathlib.
All existence steps are proved. No manuscript text or statement was changed.
Full validation passed: `lake build` completed 4161 jobs; the source audit
checked 137 Lean files; the exhaustive axiom audit checked 3301 project
declarations / 2694 theorem constants, with only the three permitted standard
foundations. Both manuscript-facing torus-identification results are explicitly
printed in the axiom report. Outstanding target checks compile; verifier output
is byte-identical; manuscript preservation and whitespace checks pass.
Self-review checked the real vector-group source, actual tangent field and
initial derivative, basis-product differential, open quotient topology,
discrete/full kernel lattice, circle period one, matching quotient kernels,
continuous inverse, and dimension-zero case.


## Fundamental highest-weight restriction (2026-09-17)

PR #46 merged at `404d1d1` after CI run `35227360294` passed. Its compact
abelian torus identification is preserved in this milestone.

`FundamentalRootWeight` closes the algebraic restriction obligation L04.
`fundamentalWeight` is the coordinate functional dual to a simple coroot in
Mathlib's root-system base. All simple-coroot pairings are proved to be the
Kronecker delta, including the manuscript's pairing equal to one.
`IsHighestWeightVector` spells out the standard nonzero weight-space and
positive-root annihilation conditions. A separate theorem derives annihilation
from absence of higher root-shifted generalized weight spaces, using Mathlib's
weight-shift theorem. No existence assertion is included in this definition.

For the standing Cartan, simple-root base, and fundamental highest-weight vector,
`root_highest_weight_one` constructs a root `sl₂` triple using the nondegenerate
Killing form. It identifies its diagonal element with the chosen coroot, proves
the vector has diagonal weight one, and proves the raising operator kills it.
`fundamental_lowering` then obtains the nonzero first lowering and zero second
lowering from the existing finite-dimensional `sl₂` theorem.

This is the manuscript's algebraic proof step, with the actual root triple
constructed rather than supplied as an extra hypothesis. It does not produce
a highest-weight group representation, a compact root subgroup, or integration
of the module. Those existence and correspondence obligations remain open in
L01/L02/L06. No general root-doublet or simple-group theorem is claimed complete.
The inventory is now 95 PROVED / 3 TODO / 7 IN PROGRESS / 5 BLOCKED = 110;
there are 135 mathematical modules.

Full validation passed: `lake build` completed 4227 jobs; the source audit
checked 138 Lean files; the exhaustive axiom audit checked 3323 project
declarations / 2709 theorem constants. Dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`. The outstanding target checks compile,
the symbolic verifier reproduces its checked-in output byte for byte, and the
manuscript is unchanged from the initial commit. Self-review checked the
root/coroot index coercions, the dual-basis normalization, the nonzero vector
condition, every positive-root annihilation condition, construction of the
actual root triple, and the finite-dimensional hypothesis for lowering.


## Complex root data from the actual real Lie algebra (2026-09-17)

PR #47 merged at `45a8958` after CI run `35228570066` passed (7m35s).
Two new modules extend the algebraic part of L01; its maximal-torus portion
remains open, so it is IN PROGRESS rather than PROVED. Inventory: 95 PROVED /
2 TODO / 8 IN PROGRESS / 5 BLOCKED = 110, with 137 mathematical modules.

`KillingBaseChange.bilinear_nondegenerate` proves preservation of nondegeneracy
under a field extension: the Gram matrix in the extended basis is the image
of the original Gram matrix, its determinant is the image of the original
nonzero determinant, and the field homomorphism is injective. Mathlib's
`LieModule.traceForm_baseChange` then identifies this form with the Killing
form of the extended Lie algebra. The resulting `IsKilling` instance is proved,
not an additional hypothesis.

`ComplexRootData` takes the actual scalar extension `ℂ ⊗[ℝ] L`. Mathlib's
regular-element theorem constructs a Cartan subalgebra; algebraic closedness
of ℂ makes it splitting. Mathlib's crystallographic root-system theorem gives
a simple-root base. Nontriviality ensures that the Cartan and its coroot basis
are nonempty, so a simple root can be chosen. Its fundamental weight is the
dual coroot coordinate, and its pairing with that coroot is proved equal to
one. The root triple is constructed in the corresponding root spaces with
diagonal element equal to the coroot.

`CompactLieRoots.simple_group_root_triple` applies the construction to
`ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G` under the manuscript's simple-Lie-algebra
condition, deriving nontriviality and nondegeneracy rather than adding them.
This wrapper actually requires no compactness or simple connectedness. Its
conclusion is an algebraic triple in the complexification. No conclusion is
made that a chosen Cartan comes from a maximal compact torus, that a compatible
compact real root form has been selected, or that an SU(2) map exists.

### Remaining geometric correspondence and covering work

The algebraic Cartan/base construction is available and is now connected to
the actual group Lie algebra. The remaining L01 task is the geometric bridge
to a maximal compact torus and a compatible real form. Constructing a Cartan
in the complexification alone does not prove that bridge. The scalar extension
proof therefore does not complete L01, L02, L06, or the visible-root-doublet lemma.

For Z05, inspected the pinned `Topology/Covering/{Basic,Quotient,Deck}` and
fundamental groupoid files. These provide covering-map definitions, local
trivializations, quotient constructions, deck transformations, and fundamental
groups. No universal-cover Lie-group construction or finite-fundamental-group
theorem for compact semisimple Lie groups was found. The simplicial universal
cover of a classifying space elsewhere in Mathlib is a different construction
and does not supply a simply connected covering Lie group of G.

Two routes were assessed. A path-class construction still needs its covering
topology, smooth group operations, and compactness of the cover; ordinary
compactness of the base does not imply compactness of an infinite-sheeted
cover. A curvature route would need the positive-Ricci calculation and
Bonnet–Myers compactness theorem. Mathlib has Riemannian metrics and path-length
infrastructure, but those curvature/compactness results were not found. A
root-lattice route instead needs the currently unproved compact torus and
group/root correspondence. None of these observations is encoded as an axiom
or as a proof of Z05; no claim of impossibility in Lean is intended.

The necessary fragment `Finite (FundamentalGroup G (1 : G))`, under compactness,
connectedness, and simplicity of the actual Lie algebra (without assuming G
simply connected), is now a type-checked outstanding target in
`scripts/CheckObligations.lean`. It does not prove or assume the finiteness claim.

Complex-root-data validation passed: full `lake build` (4254 jobs), source audit
(140 Lean files), exhaustive axiom audit (3353 project declarations / 2733 theorem
constants), outstanding-target type checks including the finite-fundamental-group
fragment, byte-identical symbolic verification, manuscript preservation, and
whitespace checks. Only `propext`, `Classical.choice`, and `Quot.sound` occur in
the dependency audit. Self-review checked the field extension, actual tensor
Lie bracket and Killing form, splitting Cartan construction, nonempty coroot
basis, normalized fundamental weight, and the actual group Lie-algebra wrapper.


## Real Cartan subalgebras and central covering steps (2026-09-17)

PR #48 merged at `6f256b5` after CI run `35229892320` passed (7m53s).
Four new mathematical modules extend L01 and Z05. The inventory is 95 PROVED /
1 TODO / 9 IN PROGRESS / 5 BLOCKED = 110; there are 141 mathematical modules.
Neither full L01 nor full Z05 is counted as proved.

`CompactCartan` proves a nilpotent Lie algebra carrying the existing anisotropic,
symmetric invariant form is abelian. Its semisimple complement to the center
is solvable because it is nilpotent; hence that complement has zero radical
and is zero. The whole algebra is therefore central. Restricting the form to
a Cartan subalgebra proves that the Cartan is abelian. Self-normalization then
proves maximality among abelian Lie subalgebras and equality with its centralizer.
The real Cartan is constructed by the regular-element theorem for the actual
group Lie algebra, and compactness supplies the already proved Haar-averaged
invariant form. No maximal torus subgroup or integration is postulated.

`DiscreteFibers.fiber_isolated` works in finite-dimensional real manifold charts.
An injective derivative has closed range and is bounded below. Mathlib's
punctured-neighborhood derivative estimate isolates the point in its fiber;
source-chart injectivity transfers this back to the manifold. Only a derivative
at the point is needed, rather than a general closed-subgroup theorem.

`SimpleGroupCenter` applies this to the actual adjoint map. Simplicity makes the
Lie-algebra adjoint representation faithful, so the already checked adjoint
differential is injective. Central elements have trivial conjugation, and hence
identity adjoint map. Thus the identity is isolated in the center. Translation
makes the center discrete; its description as the intersection of closed
commutation equalizers makes it closed. For compact Hausdorff G the center is
therefore finite. The actual quotient map `G → G ⧸ Subgroup.center G` is proved
to be a covering map using Mathlib's discrete-subgroup covering theorem.

`CentralCovering` proves a discrete normal subgroup of a connected topological
group is central: conjugation into that discrete subgroup is continuous and
therefore constant. Covering fibers are discrete, so every existing covering
homomorphism with connected source has central kernel. A surjective covering
homomorphism is open and continuous, which upgrades the algebraic first
isomorphism theorem to `G ⧸ f.ker ≃ₜ* H`. These results require no assertion
that a universal covering Lie group exists.

The remaining distinctions are essential. A maximal abelian Lie subalgebra
is not yet an actual maximal torus subgroup. Finiteness of the center of a
compact simple group is not finiteness of its fundamental group. A covering
onto its center quotient is not a construction of a compact simply connected
cover of the original group. The remaining existence/correspondence obligations
are retained explicitly. General DvK remains deferred, and the manuscript is
unchanged.

Cartan/center milestone validation passed: `lake build` completed 4258 jobs;
source audit checked 144 Lean files; exhaustive axiom audit checked 3389 project
declarations / 2765 theorem constants, with only `propext`, `Classical.choice`,
and `Quot.sound`. Outstanding target checks compile. The symbolic verifier
matches the checked-in output byte for byte, and the manuscript is unchanged.
Self-review checked the nilpotent/semisimple complement argument, actual group
Cartan and adjoint structures, isolation of a fiber rather than an unjustified
local inverse, centrality versus fundamental-group finiteness, and both directions
of continuity in the quotient equivalence. The final signatures were inspected:
the real Cartan theorem constructs the Borel measurable structure internally;
the finite-center theorem has only the actual finite-dimensional Lie-group,
simple-Lie-algebra, compactness, and Hausdorff hypotheses. No cover-existence
hypothesis is added to any general manuscript theorem.

Resume from this milestone without restarting earlier work. The remaining L01
bridge is to integrate the real Cartan to a compact torus and relate its
complexification to the root data. Z05 now has its standard central-kernel and
quotient-identification arguments, but still lacks construction and compactness
of a simply connected covering Lie group. Finite center alone does not close
that gap. L02/L06 and the deferred multivariate DvK obligations are unchanged.


## Cartan stabilizer milestone (2026-09-17)

Seven new mathematical modules extend the geometric part of L01. Inventory
remains 95 PROVED / 1 TODO / 9 IN PROGRESS / 5 BLOCKED = 110. There are 148
mathematical modules. No new manuscript obligation is claimed complete.

`BilinearStabilizer` constructs the actual subgroup of invertible continuous
linear maps preserving a bilinear operation and fixing a specified subspace
pointwise. Its joint defect has the bracket-preservation component and the
restriction of `T - 1`. The derivative kernel is exactly the derivations
vanishing on that subspace. Exponentiation preserves the bilinear operation;
a zero derivative of the orbit curve proves that it fixes every vector in the
specified subspace. The subgroup is closed in the group of units.

`StabilizerParametrization`, `StabilizerChart`, `StabilizerManifold`, and
`StabilizerLieGroup` adapt the previously checked automorphism-group construction
to these joint equations. The finite-dimensional implicit function theorem
supplies coordinates on the derivative image and kernel. Derivation
exponentials satisfy the full equations, so local injectivity proves that the
projected equations and full equations coincide near identity. Actual local
logarithm and exponential charts give a real-analytic manifold, with analytic
multiplication and inversion. The matrix embedding is analytic and its
identity differential is the inclusion of the kernel subspace. No generic
closed-subgroup theorem or subgroup manifold structure is assumed.

`CartanStabilizer` specializes to a finite-dimensional real Killing Lie algebra
with an abelian Cartan. Every derivation is inner by Mathlib's Killing-algebra
theorem. Vanishing on the Cartan puts its inner element in the Cartan, by the
already proved self-centralizing characterization. These tangent derivations
commute, and so do their exponentials. The local chart then yields a commuting
neighborhood in the actual pointwise stabilizer group.

`LocalCommutativity` proves that a topological group with a commuting identity
neighborhood has abelian identity component. Each relevant centralizer contains
an identity neighborhood and is therefore open and closed. It contains the
identity component; applying this observation twice proves commutativity.
This completes the stabilizer identity-component claim without assumptions of
global connectedness or local connectedness on an arbitrary topological group.

Validation passed: `lake build` completed 4265 jobs; source audit checked 151
Lean files; exhaustive axiom audit checked 3536 project declarations / 2894
theorem constants, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
Outstanding obligation statements compile. The symbolic verifier reproduces
its checked-in output byte for byte. The mathematical manuscript is unchanged.
Self-review checked both defect equations, the image/kernel local-inverse
argument, the actual subgroup chart topology and smooth operations, the sign
in the inner-derivation convention, and both centralizer arguments.

The next L01 tasks are compactness of the relevant stabilizer component,
its relation to the original compact group via the adjoint map, and the
maximal-torus and complex-root correspondence. An abelian identity component
alone is not yet the manuscript's maximal compact torus. Z05, L02/L06, and
the deferred general DvK obligations remain as previously documented.


## Compact Cartan torus milestone (2026-09-17)

Five new mathematical modules extend L01. Inventory remains 95 PROVED / 1 TODO /
9 IN PROGRESS / 5 BLOCKED = 110. There are 153 mathematical modules. The torus
constructed here lies in the automorphism group of the actual group Lie algebra;
full L01 is still IN PROGRESS.

`FullAdjoint` extends the earlier simple-factor argument to the full group Lie
algebra. The actual adjoint representation is a smooth homomorphism into its
bilinear automorphism Lie group. The differential at identity is the adjoint
Lie-algebra map. For a Killing Lie algebra every derivation is inner, making
this differential surjective. Hence the group image is open. For connected G,
the image is connected and equals the automorphism identity component, since
an open subgroup is clopen. Compactness of G then proves that this component
is compact. The homomorphism itself requires neither compactness nor a Killing
hypothesis; those enter only the relevant later conclusions.

`StabilizerCompact` proves that the inclusion of the pointwise stabilizer into
the bilinear automorphism group is a closed embedding. Its range is the
intersection of the vector-fixing equalizers. A continuous map sends an identity
component into the identity component, so the stabilizer component is a closed
subset of the preimage of the compact automorphism component. This proves its
compactness without claiming the whole automorphism group is compact.

`CartanTangent` proves that the adjoint map from an abelian Cartan to its
stabilizer tangent model is a linear equivalence in the Killing case. Innerness
and self-centralization supply surjectivity; faithfulness of the adjoint map
supplies injectivity. Thus the tangent model has exactly the Cartan dimension.

`StabilizerTorus` uses local connectedness of the already constructed manifold
to make the identity component an open subgroup. Its restriction charts give
an actual smooth Lie group. It is connected, compact by the preceding result,
and abelian by the earlier exponential/centralizer proof. Applying the already
proved compact abelian classification constructs its continuous group
equivalence with a torus of Cartan dimension.

`CompactCartanTorus.component_torus` applies all this to the real Cartan already
constructed from the actual Lie algebra of a compact connected simple group.
Its final signature assumes only the actual finite-dimensional real Lie-group
structure, compactness, connectedness, and simplicity of the group Lie algebra.
It constructs the topological-group instance internally. It assumes no Cartan,
torus, compact stabilizer, or existence of a root subgroup.

Validation passed: `lake build` completed 4270 jobs; source audit checked 156
Lean files; exhaustive axiom audit checked 3615 project declarations / 2960
theorem constants, with only `propext`, `Classical.choice`, and `Quot.sound`.
Outstanding statement checks compile, the symbolic verifier matches its
checked-in output exactly, and the mathematical manuscript is unchanged.
Self-review checked the actual adjoint map and differential, image/component
equality, closed embedding and compact-preimage argument, the Cartan/tangent
linear equivalence, inherited component charts, and the final wrapper signature.

The remaining bridge is to lift the constructed automorphism torus to the
original compact group and prove maximality, then align its complexified Cartan
with the root data. The established finite center and injective adjoint
differential are available for a local-inverse or covering construction. No
maximality or lift is asserted in this milestone. Z05, L02/L06, and deferred
general DvK remain as documented; progress here does not change their status.


## Cartan maximality and connected preimage milestone (2026-09-17)

Four new mathematical modules extend L01. Inventory remains 95 PROVED / 1 TODO /
9 IN PROGRESS / 5 BLOCKED = 110. There are 157 mathematical modules. Maximality
in the automorphism group is now proved; maximality in the original group is
not yet claimed.

`CartanMaximal` maps the stabilizer component into the actual automorphism group.
Every tangent exponential lies in that component, since the exponential map
has connected domain and takes zero to identity. An automorphism commuting
with the component commutes with each one-parameter exponential. Differentiating
this identity proves that it commutes with the corresponding tangent derivation.
For derivations from the Cartan, bracket preservation and faithfulness of the
adjoint representation then force the automorphism to fix the Cartan pointwise.
Thus any connected abelian subgroup containing the component image maps into
the pointwise stabilizer and, by connectedness, into its identity component.
It equals the component image. Commutativity of that image is separately proved
from the existing abelian identity-component theorem.

`AdjointCovering` proves that the full adjoint kernel equals the center for any
connected real group in scope. A trivial adjoint operator says conjugation and
the identity have the same differential, so the proved uniqueness theorem for
smooth homomorphisms makes conjugation trivial. The reverse direction follows
by differentiating the trivial conjugation map. The algebraic first isomorphism
theorem, quotient continuity, and compact-to-Hausdorff inverse continuity give
a topological equivalence from the quotient by the kernel to the actual image.
For a compact Hausdorff group with simple Lie algebra, the already proved
discrete center makes the quotient map a covering. Composing its local
homeomorphisms with the equivalence gives the covering onto the adjoint image.
This is not a construction of a simply connected cover and does not close Z05.

`DiscreteKernel` proves that commutativity of an image lifts on a connected
source through a discrete kernel. Fixing one argument, the commutator is a
continuous function into the kernel; it is constant and equals its identity
value. Neither a covering map nor centrality of the kernel is assumed by this
intermediate lemma.

`CartanLift` constructs the subgroup preimage in G of the actual Cartan torus
image and then its identity component. The torus image is compact, hence closed
in the automorphism group. Its preimage is closed in compact G, and its identity
component is therefore compact and connected. The inclusion into G is a
continuous injective homomorphism. The image is abelian, and the adjoint kernel
is the discrete center, so the discrete-kernel lemma proves abelianness of this
connected preimage. Its explicit topological-group instance is the standard
one already supplied by a Lie group; no additional existence input is used.

Validation passed: `lake build` completed 4274 jobs; source audit checked 160
Lean files; exhaustive axiom audit checked 3664 project declarations / 2998
theorem constants, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
Outstanding target statements compile. The verifier output is unchanged byte
for byte, and the mathematical manuscript is unchanged. Self-review checked
exponential connectedness, differentiation of commutation, the faithful-adjoint
step, the essential connectedness hypothesis in maximality, quotient topology,
the precise covering target, and constancy of the kernel-valued commutator.
The critical final signatures were inspected.

Next, restrict the adjoint covering over the torus, construct the lifted Lie
charts, and prove that the connected preimage surjects onto the torus. These
will permit torus identification and maximality in the original group. The
complex Cartan/root correspondence also remains open. A compact connected
abelian subgroup alone is not being substituted for the full maximal-torus
obligation. The deferred DvK, L02/L06, and Z05 gaps remain documented.


## Maximal torus in the original group (2026-09-17)

PR #52 merged at `e53846f` after CI run `35237039303` passed (9m38s).
Three new mathematical modules extend L01. Inventory remains 95 PROVED /
1 TODO / 9 IN PROGRESS / 5 BLOCKED = 110; there are 160 mathematical modules.
An actual maximal torus in the original compact connected simple Lie group is
now constructed. L01 remains in progress because compatibility with the
complexified Cartan and root data has not yet been established.

`CoveringCharts` pulls charts back along a local homeomorphism to a real
manifold. The chosen local inverse yields open partial homeomorphisms whose
forward maps are target charts composed with the original map. On overlaps,
the inverse identity reduces transitions locally to the target's smooth
transitions. This proves the manifold structure and smoothness of the original
map. Continuity together with smoothness after composition gives smoothness
into the pulled-back atlas. Applied to multiplication and inversion, this
constructs a Lie-group structure for a topological group admitting a locally
homeomorphic homomorphism into a Lie group. No pre-existing smooth structure
on the source is required.

`CartanCovering` first combines the covering onto the adjoint image with the
open inclusion of that image in the actual automorphism group. Compactness
makes the resulting local homeomorphism a covering. Restriction to the Cartan
torus gives a covering from its actual subgroup preimage. The stabilizer
component is continuously and injectively mapped onto its image; compactness
and Hausdorffness give the topological group equivalence used to identify the
covering target with that component. Pulling back its charts gives the
preimage a Lie-group structure. Its identity component is open by local
connectedness, so it inherits that Lie structure. The previously proved
compactness, connectedness, and abelianness then identify this lift with a
torus, with dimension equal to the real Cartan.

`CartanLiftMaximal` restricts the covering to the open identity component.
Its homomorphism has open image in the connected Cartan component, hence is
surjective. A connected abelian subgroup of G containing the lift therefore
has adjoint image containing the whole Cartan torus. The earlier maximality
proof in the automorphism group forces this image to equal the Cartan torus.
The subgroup consequently maps into its preimage, and connectedness places it
inside the identity component. This proves maximality in G. The final wrapper
constructs an actual subgroup of G topologically isomorphic to the torus and
maximal among connected abelian subgroups, deriving the topological-group
instance from the given Lie-group structure.

The manuscript is unchanged. These steps do not construct a simply connected
cover, a highest-weight group representation, or a root SU(2) subgroup. General
DvK remains deferred under the user's direction. The next L01 step is to relate
the real Cartan to a splitting Cartan in its complexification and to align that
algebraic data with the constructed maximal torus.

Validation passed: full `lake build` (4277 jobs), source audit (163 Lean files),
exhaustive dependency audit (3748 project declarations / 3070 theorem constants),
and compilation of outstanding target statements. The only axioms found are
`propext`, `Classical.choice`, and `Quot.sound`. The symbolic verifier reproduces
its checked-in output byte for byte. Manuscript preservation and whitespace
checks passed. Self-review checked the pulled-back chart domains and overlaps,
the actual adjoint covering restriction, the compact-to-Hausdorff equivalences,
openness and surjectivity of the identity-component map, and the final wrapper's
assumptions and maximality quantifiers. The maximal-torus wrapper assumes only
the finite-dimensional compact connected Hausdorff real Lie-group setting and
simplicity of its actual Lie algebra; it does not assume the existence of the
torus or its smooth structure.


## Compatible maximal torus and complex roots: L01 complete (2026-09-17)

PR #53 merged at `d7199cf` after CI run `35239046813` passed (9m19s).
Six new mathematical modules complete L01. Inventory is now 96 PROVED /
1 TODO / 8 IN PROGRESS / 5 BLOCKED = 110, with 166 mathematical modules.
The checked setup applies already to compact connected Hausdorff simple Lie
groups; simple connectedness is not needed for this obligation. It is needed
by the separate highest-weight group representation step, which remains open.

`ComplexCartan` constructs real and imaginary projections on the actual tensor
complexification and proves its two-component decomposition and bracket formulas.
A complex Lie subalgebra is defined by requiring both components to lie in the
real subalgebra. It is proved equal to the usual scalar-extension submodule.
Normalizer membership implies that both real components normalize the original
Cartan, so self-normalization descends directly. Abelianness also extends, giving
a nilpotent, self-normalizing complex Cartan. This specialized argument supplies
the base-change result missing from the inspected Lie-library API.

`CompatibleRootData` uses this complexification of the same real Cartan used
in the torus construction. Mathlib constructs its simple-root base; the existing
fundamental-weight construction gives coroot pairing one and a normalized root
triple. The actual compact simple-group wrappers make the real/complex Cartan
membership relation explicit. No unrelated complex Cartan is chosen in this
compatible setup.

`SmoothLift` proves a local smoothness criterion via the inverse function
theorem: a continuous map whose composition with a smooth map of invertible
differential is smooth is itself smooth locally. The proof first uses the
normed-space local inverse and then transports the criterion through manifold
charts. `CoveringDifferential` proves that a covering map has identity
differential in the pulled-back charts.

`CartanDifferential` proves smoothness of the Cartan component inclusion in the
automorphism group and computes its matrix differential. The adjoint map's
bijective differential and the local smoothness criterion prove smoothness of
the lifted torus inclusion at identity; translations give global smoothness.
Differentiating its adjoint factorization shows that a lifted tangent vector
acts by the corresponding inner derivation. Faithfulness of the adjoint
differential identifies the torus inclusion differential with inclusion of the
original real Cartan. Its range is exactly that Cartan and it is injective.

`CompactRootSetup.maximal_torus_root_setup` combines the torus equivalence,
smooth injective inclusion, injective differential, maximality, real/complex
Cartan compatibility, and fundamental-weight normalization into one checked
manuscript-facing setup. Thus the algebraic roots now belong to the actual
tangent Cartan of the constructed maximal torus. The earlier arbitrary-Cartan
root construction remains valid as a general algebraic result; this wrapper
uses the compatible construction instead.

Downstream review: the weight-one restriction theorem accepts arbitrary Cartan
and simple-base data, so it applies to the new compatible data. L02 still needs
the actual highest-weight group representation and L06 still needs root SU(2)
integration. Their existence is neither assumed nor supplied by L01. Z05 still
needs a compact simply connected cover. General DvK remains deferred. No
manuscript statement or proof has been changed.

Validation passed: full `lake build` (4283 jobs), source audit (169 Lean files),
and exhaustive axiom audit (3848 project declarations / 3153 theorem constants).
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the dependencies.
Outstanding target statements compile. The exact symbolic verifier still
matches its checked-in output byte for byte; the manuscript remains identical
to the initial source of truth. Whitespace checks passed. Self-review inspected
scalar-extension membership, both normalizer components, the inverse-function
hypotheses, chart differentials, the adjoint chain rule, tangent range equality,
and the combined setup's actual assumptions. The explicit topological-group
instance is supplied by a Lie group and is not an additional existence premise.
The ledger row count was recomputed as 96 / 1 / 8 / 5 = 110.
