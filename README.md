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

The Lean formalization is in progress; the main classification is **not yet formalized**.
The Hopf coefficient theorem, sphere marker tower, and universal radial-transfer theorem are kernel-checked, along with the representative-algebra and Haar-pullback lemmas. The explicit SU(2) counterexample, the closed-form SU(n)/Sp(n) witnesses, and the transformed Laurent witness’s full integral correspondence are also checked. The representative-function/Laurent algebra equivalence for finite-dimensional tori and its Haar constant-term identity are proved; the higher-rank Duistermaat–van der Kallen step remains open.
The 2025 Zwart SU(N), Sp(N), and G₂ abelian conjectures are directly refuted, with their source coefficient algebras, dimensions, densities, and radial integral correspondences.
See [the obligation ledger](FORMALIZATION_STATUS.md) for exact coverage and outstanding dependencies.
The toolchain and mathlib revision are pinned. Build and audit the current proofs with:

```sh
lake build
python3 scripts/audit_sources.py
lake env lean scripts/AxiomAudit.lean
python3 scripts/verify_mathieu_classification.py
```

Auxiliary tooling and its checked-in outputs live under `scripts/`.

## Provenance

The project was migrated from [`octonion/mathematics/mc`](https://github.com/octonion/mathematics/tree/main/mc). The original subtree was introduced in commit [`7573e57a16fe85177d8a4dab9d98a681923af918`](https://github.com/octonion/mathematics/commit/7573e57a16fe85177d8a4dab9d98a681923af918). The repository history there remains the archival record of the former location.

The one-variable Duistermaat–van der Kallen theorem and the actual circle
Mathieu property are now proved in `MathieuProperty/OneVariableTorus.lean`.
The valuation and partial-fraction proof is adapted from the MIT-licensed
[MurrellGroup/GMC-2-lean](https://github.com/MurrellGroup/GMC-2-lean/tree/1782de7ff6c97eb1d98e63e7ff34df18b9cd322e),
rebuilt and axiom-audited on this project's pinned toolchain. Higher-rank DvK
and the full torus corollary remain open.
