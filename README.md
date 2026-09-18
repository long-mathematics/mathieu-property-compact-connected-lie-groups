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

## Lean formalization

This repository is the canonical development location for the paper and its Lean formalization.

### Current status

The **main classification theorem is fully formalized conditional on one explicit mathematical input**, the multivariate Duistermaat--van der Kallen theorem for complex Laurent polynomials. The checked dependency chain is

$$
\texttt{MultivariateDvK}
\;\Longrightarrow\;
\text{Mathieu property for compact tori}
\;\Longrightarrow\;
\text{full compact-connected classification}.
$$

The interface [`MultivariateDvK`](MathieuProperty/DvKStatement.lean) states the Laurent-polynomial theorem used by the manuscript. The theorems [`torus_mathieu_of_dvk` and `classification_of_dvk`](MathieuProperty/ConditionalClassification.lean) establish the two implications above with that hypothesis as the sole unproved mathematical input to the main classification.

The unconditional multivariate DvK theorem, and therefore the unconditional torus theorem and full classification, remain open in this repository. The entire manuscript is not claimed to be fully formalized: several manuscript-specific constructions remain outside the main classification dependency path. Exact coverage is recorded in the [formalization ledger](FORMALIZATION_STATUS.md).

### Checked coverage

The formalization currently includes, among other results:

- the representative-function algebra, normalized Haar integration, and Haar pullback;
- the Hopf coefficient theorem, sphere marker tower, and universal radial-transfer theorem;
- the explicit SU(2) counterexample and the closed-form SU(n) and Sp(n) witness families;
- the compact Lie-algebra decomposition, adjoint simple quotient, and the full uniform nonabelian marker tower;
- the implication that the Mathieu property forces a compact connected Lie group to be abelian;
- the identification of compact connected abelian Lie groups with finite-dimensional tori;
- the representative-function/Laurent-polynomial correspondence for tori and the Haar constant-term identity;
- the one-variable Duistermaat--van der Kallen theorem and the circle Mathieu property;
- the paper's abelian-reduction counterexamples, with the SO(N) case using the documented Euler-consistent correction described in the ledger.

The nonabelian half of the classification is unconditional. Some original manuscript constructions involving general highest-weight representations, root integration, and related covering data remain unformalized, but they are not required by the checked main-classification route.

### Verification

The Lean toolchain and mathlib revision are pinned. Build and audit the current development with:

```sh
lake build
python3 scripts/audit_sources.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/CheckAdjointRoute.lean
lake env lean scripts/CheckConditionalClassification.lean
python3 scripts/verify_mathieu_classification.py
```

Auxiliary verification and audit tooling, together with checked-in outputs where applicable, lives under `scripts/`.

## Provenance

The project was migrated from [`octonion/mathematics/mc`](https://github.com/octonion/mathematics/tree/main/mc). The original subtree was introduced in commit [`7573e57a16fe85177d8a4dab9d98a681923af918`](https://github.com/octonion/mathematics/commit/7573e57a16fe85177d8a4dab9d98a681923af918). The repository history there remains the archival record of the former location.
