# Word representability formalization for Lax

This separate package formalizes the characterization of word-representable graphs by Halldórsson, Kitaev and Pyatkin (HKP), together with their corrected clique bound. A noncomplete word-representable graph with $n$ vertices and clique number $\omega$ has a $2(n-\omega)$-uniform representation.

## Public statements

The concept modules expose four statements:

- A word representation induces a semi-transitive orientation, without a finiteness assumption.
- A finite semi-transitively orientable graph admits a positive uniform representation.
- A finite graph is word-representable if and only if it is semi-transitively orientable.
- A finite noncomplete word-representable graph admits a representation of multiplicity exactly $2(n-\omega)$.

The two foundational concepts define words and semi-transitive orientations. The proof network combines the forward and converse implications for the characterization; the clique bound uses the forward implication and the corrected HKP construction.

## Provenance and license

The ten helper modules in `proofs/Lax458700Proofs` are the transitive dependency slice of `FiniteConverse.lean` and `HKPBound.lean` from [Word-representable-graphs](https://github.com/magnusmhalldorsson/Word-representable-graphs/tree/8089abbf6bbcc85911a0cdc184c63d8c28bcf3d3), a private source repository, commit `8089abbf6bbcc85911a0cdc184c63d8c28bcf3d3`. Their package imports and namespace have been changed to `Lax458700Proofs`, and introductory comments expand the abbreviation HKP. Their mathematical declarations and proofs are unchanged. The archive bridge proves that the public definitions express the same properties as the original structures.

The original development uses Lean 4.34.1. This export targets Lax's Lean 4.33.0 environment with mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. All ten copied modules compile without mathematical changes.

Apache License 2.0 applies to this exported package only, as authorized by Magnús Már Halldórsson. The original repository's license, source files, and toolchain have not been changed. The mathematical source is Halldórsson, Kitaev and Pyatkin, [Semi-Transitive Orientations and Word-Representable Graphs](https://arxiv.org/abs/1501.07108), Discrete Applied Mathematics 201 (2016), 164–171.

## Local validation

Run `lax build . --replay --no-color` from this folder. Lax requires a local Git checkpoint even for a local build. Its concept statement declarations use the archive's required `axiom` syntax; the four annotated proofs discharge them, with acyclic dependencies between statements.

Local validation passed on 7 October 2026, including compilation, independent kernel replay, and inspection of all six concepts and four proofs. Both directional proofs have no archive-statement assumptions; the characterization and clique bound depend only on those independently proved statements.

Lax reports 66 nonblocking unused-helper warnings. The full source-module slice is intentionally retained for comparison with the original development; the warnings include automatically generated structure lemmas and results about comparability and permutation graphs that are not public claims of this export. No `sorry`, `native_decide`, or proof-package axioms occur.

Formalization author: Magnús M. Halldórsson, Reykjavik University. The manifest records the author's name; the abstract carries the affiliation because Lax has no separate affiliation field.

A Lax draft may be updated. Permanent registration is a separate step.
