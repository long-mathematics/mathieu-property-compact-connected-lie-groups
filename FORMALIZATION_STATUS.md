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

- Development branch: `formalization/hopf-coordinate-measure`; prior foundation milestone [PR #1](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/1). Use `git status` for the live checkout after merging.
- Lean: `leanprover/lean4:v4.34.0`.
- mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0).
- M0 and M1 complete; the library covers 62 mathematical modules plus the import umbrella. The Hopf coefficient theorem, sphere marker tower, and universal radial-transfer theorem are proved, as are the representative-algebra and Haar-pullback lemmas. The main classification, uniform nonabelian tower, root subgroup existence, and torus direction remain outstanding. The exact Hopf coordinate-density obligation H05 is now proved as well; the original sphere theorem retains its documented invariant-moment proof.
- Milestones through the earlier weighted xz witness are merged and CI-checked ([PR #23](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups/pull/23)). The general classification remains unproved; ordinary obligations continue alongside investigation of the foundational gaps. No weakening or conditional main theorem is authorized.
- No manuscript mathematical error has been identified. The detailed investigation below records missing Duistermaat–van der Kallen and representation/root-integration infrastructure. These remain formalization gaps; no cited result is assumed, and the audited manuscript is unchanged.

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
| prop:adjoint-simple-quotient | Every nonabelian compact connected Lie group surjects continuously onto adjoint compact simple group | adjoint_simple_quotient | AdjointQuotient | G01–G06 | TODO | Manuscript |  |
| thm:uniform-nonabelian | Full manuscript quantifiers, representative triple and radial moment tower, positivity and vanishing | uniform_nonabelian | MainTheorem | prop:adjoint-simple-quotient; cor:simple-central-forms; lem:haar-pullback | TODO | Manuscript |  |
| thm:dvdk | Nonzero complex multivariate Laurent f with all positive-power constant terms zero has Newton polytope avoiding zero | duistermaat_van_der_kallen | Torus | T04 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| cor:torus | Every torus has the Mathieu property | torus_mathieu | Torus | T01–T08; thm:dvdk | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| thm:classification | For every compact connected Lie group: Mathieu property iff abelian iff torus | classification | MainTheorem | thm:uniform-nonabelian; cor:torus; T01 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| prop:explicit-abelian-SU2 | Transformed Laurent pair: exact moments, printed expansion, exact spectrum | Abelian.formal_expansion; Abelian.formal_spectrum | AbelianAlgebra / AbelianLaurent | E01–E09; thm:hopf-coefficient | IN PROGRESS | Manuscript | Algebra, spectrum, and exact weighted moment formulas checked; external transform correspondence pending. |
| cor:abelian-reductions | Failure of both universal abelian conjectures, growth claim and specified Zwart reductions | Abelian.universal_moment_conjecture_false; Abelian.universal_convex_support_conjecture_false; Abelian.universal_growth_conjecture_false | AbelianConjectures | E10–E14; prop:explicit-abelian-SU2; thm:classification | IN PROGRESS | Direct witness | Both universal conjectures and the stronger growth assertion are refuted. Specified Zwart reductions remain open. |
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
| L01 | Maximal torus, simple roots and fundamental weight with coroot pairing one | fundamental_weight_pairing | RootSU2 |  | TODO | Manuscript |  |
| L02 | Simply connected compact simple group admits irreducible representation of fundamental highest weight | fundamental_representation_exists | RootSU2 | L01 | BLOCKED | Manuscript | Missing foundational infrastructure; see detailed obstruction investigation below. No proof or assumption added. |
| L03 | Average inner product to obtain invariant Hermitian metric | averagedInnerCore; unitaryModel_intertwines; unitaryModel_continuous; invariantInnerProduct_invariant; invariantInnerProduct_continuous | HaarUnitarization | D-haar | PROVED | Manuscript | Haar average is positive definite and invariant; arbitrary finite-dimensional complex normed representations have a continuous unitary model, continuously linearly equivalent to the original representation. |
| L04 | Root sl₂ action on highest vector has weight one | root_highest_weight_one | RootSU2 | L01; L02 | TODO | Manuscript |  |
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
| E10 | Earlier weighted xz witness has zero pure moments and (-1)^(m-1)/(2(m+1)) marker; spectrum {-1,0,1} | Abelian.weighted_xz_witness; Abelian.earlierXZ_specialize; Abelian.earlierXZ_spectrum | EarlierXZ | beta integral; phase coefficient interpretation | PROVED | Direct binomial/beta proof | Exact formal Laurent polynomial f₀(x²,w), pure and marked weighted integrals, nonzero marker for every m≥1, and exact formal spectrum. No external moment theorem is assumed. |
| E11 | Definitions and admissibility of universal moment and convex-support conjectures | Abelian.UniversalMomentConjecture; Abelian.UniversalConvexSupportConjecture; Abelian.coordinate_weight_admissible; Abelian.mixedIntegral_eq_circle_integral | AbelianConjectures / MixedPhase | E05; E14 (definitions only) | PROVED | Direct witness at N=M=1, δ=x | Arbitrary dimensions, polynomial coefficient ring, actual cube integral and normalized product-circle correspondence; both conjectures refuted. |
| E12 | Zero pure moment sequence has zero limsup growth, contradicting asserted positive growth | Abelian.weightedCT_growth_zero; Abelian.universal_growth_conjecture_false | AbelianConjectures | E05; E11 | PROVED | Manuscript | Actual real limsup of the complex moment norm raised to 1/m; m=0 handled by eventual equality. |
| E13 | Each specified Zwart abelian implication formally stated and proved, then contraposition | zwart_reductions_false | AbelianWitness | E14; thm:classification | TODO | Manuscript |  |
| E14 | External Mueger–Tuset Lemma 5.2, Prop 5.3, Conjectures 6.3/6.6, Remark 6.7; Zwart implications: exact definitions and needed results | external_reduction_correspondence | AbelianWitness |  | IN PROGRESS | Source definitions and direct circle-integral proof | Conjectures 6.3/6.6 and growth assertion defined and refuted. Lemma 5.2, full Prop. 5.3 correspondence, and Zwart implication theorems remain open. |

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


Current inventory counts: PROVED=81, TODO=17, IN PROGRESS=6, BLOCKED=6 (110 rows).

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
