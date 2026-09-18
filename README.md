# The Mathieu Property for Compact Connected Lie Groups

## Abstract

Let $G$ be a compact connected Lie group, let $\mathcal R(G)$ denote its algebra of representative functions, and let $\mathcal I_G(f)=\int_G f(g)\,\mathrm d g$ be normalized Haar integration. We prove that $\ker \mathcal I_G$ is a Mathieu--Zhao subspace of $\mathcal R(G)$ if and only if $G$ is a torus. More strongly, for every nonabelian compact connected Lie group $G$ we construct $A,P,Q\in\mathcal R(G)$, with $A\geq 0$ and $A\not\equiv 0$, such that all pure moments of $P$ vanish and the marked moments satisfy an exact Pascal-row identity

$$
\mathcal I_G(Q^sP^m)
=c_m\binom{m-1}{s-1}\mathcal I_G(A^{4m+s})>0
\qquad (1\leq s\leq m),
$$

where $c_m=4^m(m!)^2/(2m+1)!$; the same moments vanish for $s>m$.

## Preprint and source

- [arXiv:2609.16178](https://arxiv.org/abs/2609.16178)
- [Preprint PDF](https://arxiv.org/pdf/2609.16178)
- [LaTeX source](mathieu_property_compact_connected_lie_groups.tex)
- [Exact verification script](scripts/verify_mathieu_classification.py)
- [Verification output](scripts/verify_mathieu_classification.txt)

## Formalization

This repository is the canonical development location for the paper and its Lean formalization.

- **Current status.** The Lean formalization is in progress. The **main classification is formalized relative to one explicit multivariate DvK hypothesis**; its unconditional proof remains open.

- **Core analytic and representative-function results.** The Hopf coefficient theorem, sphere marker tower, and universal radial-transfer theorem are kernel-checked, along with the representative-algebra and Haar-pullback lemmas. The explicit SU(2) counterexample, the closed-form SU(n)/Sp(n) witnesses, and the transformed Laurent witness’s full integral correspondence are also checked. The representative-function/Laurent algebra equivalence for finite-dimensional tori and its Haar constant-term identity are proved; the higher-rank Duistermaat–van der Kallen step remains open.

- **Abelian reductions.** The 2025 Zwart SU(N), Sp(N), and G₂ abelian conjectures are directly refuted, with their source coefficient algebras, dimensions, densities, and radial integral correspondences. The older fractional SU(N), Sp(N), and G₂ conjectures are also refuted with actual punctured-circle integrals. The SO(N) conjecture is refuted under the explicitly approved Euler-consistent correction of Zwart 2023: N−2 new radial variables, powers (k−1)/2, and recursion beginning at x_(N−1). The transformed finite-type function uses the same corrected split. This is a correction of the source, not literal equality with its malformed printed recurrence; the original discrepancy is preserved in the ledger. The combined abelian-reductions corollary is checked with this interpretation.

- **Compact Lie infrastructure.** The compact Lie-algebra decomposition and the adjoint simple quotient proposition are also proved: every nonabelian compact connected Lie group surjects onto an actual compact connected centerless Lie group with simple Lie algebra. The identification of compact connected abelian Lie groups with finite-dimensional tori is now also proved, including dimension zero. The algebraic restriction of a fundamental highest-weight vector to a root sl₂ triple is also proved, with the root triple constructed from the Cartan data. Complexification, an algebraic Cartan subalgebra, and a simple-root base are now constructed from the actual simple group Lie algebra; an abelian, self-centralizing real Cartan is also constructed, and its pointwise automorphism stabilizer component is now proved to be a compact torus of the same dimension as the Cartan. This torus is maximal among connected abelian automorphism subgroups. Its preimage identity component now inherits a Lie-group structure through the adjoint covering, is a torus of Cartan dimension, and is maximal among connected abelian subgroups of the original group. The torus inclusion is smooth with differential image equal to that real Cartan; its complexification is the splitting Cartan used for the simple-root base and normalized fundamental weight. This completes the maximal-torus/root-data setup. Compact simple groups are proved to have finite center, and surjective covering homomorphisms with connected source are identified with central topological quotients. The general highest-weight representation, root integration, and covering steps remain outstanding. General multivariate DvK is deferred pending the externally developed resolution-free proof; no Hironaka formalization is being attempted.

- **Nonabelian half of the classification.** The adjoint alternative now proves the **full uniform nonabelian marker tower** and the implication **Mathieu property ⇒ abelian**. At rank at least two it constructs the root-string doublet, compact-real generators, and invariant coordinate pushforward directly from the actual group. At rank one it proves the concrete identification of the center quotient with SU(2)/{±1}, then pulls back the central quotient witness. The rank split applies directly to the constructed adjoint simple quotient of any nonabelian compact connected Lie group.

- **Proof substitution and remaining dependency.** This removes L02 (fundamental highest-weight existence), L06 (general root-subgroup integration), and Z05 (compact simply connected covering) from the main classification dependency path. Those original manuscript ingredients remain unformalized, and the alternative does not identify its witnesses with the source’s specified fundamental-representation functions. All four adjoint bridge targets, including rank-one AR03, and the expanded uniform tower conclusion are checked in [scripts/CheckAdjointRoute.lean](scripts/CheckAdjointRoute.lean). The unconditional general torus direction, dependent on deferred multivariate DvK, remains the missing half of the classification.

- **Conditional main theorem.** `MultivariateDvK` states the exact complex Laurent-polynomial theorem. `torus_mathieu_of_dvk` and `classification_of_dvk` prove the complete torus and main-classification implications with that explicit parameter, without adding an axiom. Thus general multivariate DvK is the only remaining unproved input to the **main classification**. Its resolution-free proof is ongoing in a separate project. The unconditional torus theorem and classification remain blocked, and the entire manuscript is not claimed complete conditional on DvK. See [the conditional interface](MathieuProperty/DvKStatement.lean), [the classification endpoint](MathieuProperty/ConditionalClassification.lean), and [the independent endpoint check](scripts/CheckConditionalClassification.lean).

- **One-variable DvK.** The one-variable Duistermaat–van der Kallen theorem and the actual circle Mathieu property are now proved in `MathieuProperty/OneVariableTorus.lean`. The valuation and partial-fraction proof is adapted from the MIT-licensed [MurrellGroup/GMC-2-lean](https://github.com/MurrellGroup/GMC-2-lean/tree/1782de7ff6c97eb1d98e63e7ff34df18b9cd322e), rebuilt and axiom-audited on this project's pinned toolchain. Higher-rank DvK and the unconditional full torus corollary remain open.

See [the obligation ledger](FORMALIZATION_STATUS.md) for exact coverage and outstanding dependencies.

The toolchain and mathlib revision are pinned. Build and audit the current proofs with:

```sh
lake build
python3 scripts/audit_sources.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/CheckAdjointRoute.lean
lake env lean scripts/CheckConditionalClassification.lean
python3 scripts/verify_mathieu_classification.py
```

Auxiliary tooling and its checked-in outputs live under `scripts/`.

## Provenance

The project was migrated from [`octonion/mathematics/mc`](https://github.com/octonion/mathematics/tree/main/mc). The original subtree was introduced in commit [`7573e57a16fe85177d8a4dab9d98a681923af918`](https://github.com/octonion/mathematics/commit/7573e57a16fe85177d8a4dab9d98a681923af918). The repository history there remains the archival record of the former location.
