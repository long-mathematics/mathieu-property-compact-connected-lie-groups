# Repository instructions

This repository contains the mathematical research preprint **The Mathieu Property for Compact Connected Lie Groups** and its Lean formalization.

## Primary document

The mathematical source of truth is `mathieu_property_compact_connected_lie_groups.tex`.

The published preprint is arXiv:2609.16178.

## Mathematical integrity

- Do not alter theorem, proposition, lemma, corollary, definition, or conjecture statements unless explicitly instructed.
- Do not silently weaken or strengthen hypotheses or conclusions.
- Do not silently repair a suspected mathematical error. Flag it and explain the issue first.
- Preserve mathematical notation unless a task explicitly concerns notation.
- When changing a proof, inspect downstream results that depend on the changed argument.
- Distinguish substantive mathematical changes from editorial, typographical, repository, and formalization changes.
- The TeX manuscript remains the mathematical source of truth for the formalization unless an explicit mathematical correction is approved.

## Lean formalization

- Formalize manuscript results faithfully, with manuscript-facing wrapper theorems when Lean-native internal statements differ syntactically.
- Never use `sorry`, `admit`, or project-added axioms to finish a proof.
- Search mathlib before reproving substantial standard results.
- Prefer Lean-native proofs when they prove the same mathematical claim more cleanly; document material proof substitutions.
- Maintain a theorem/proof coverage ledger during substantial formalization work.
- Run `lake build` regularly and before completing any formalization milestone.
- Audit project-owned Lean sources for `sorry`, `admit`, and explicit added `axiom` declarations before merging.

## LaTeX conventions

- Preserve the existing document style and notation.
- Do not introduce unnecessary packages or macros.
- Keep existing labels stable whenever possible.
- Resolve broken references and citations caused by edits.
- The bibliography is contained directly in the TeX source; there is no external `.bib` file.

## Verification script

`verify_mathieu_classification.py` contains exact symbolic checks supporting displayed identities in the manuscript. Changes to those identities should be checked against this script where applicable.

## Git workflow

- Use feature branches and pull requests for substantive work after repository initialization.
- Keep `main` releasable and buildable.
- Prefer squash merging for coherent formalization milestones.
- Do not force-push or rewrite published history unless explicitly instructed.

## Generated files

Do not commit LaTeX auxiliary files, Lean/Lake build products, Python caches, or other generated caches.
