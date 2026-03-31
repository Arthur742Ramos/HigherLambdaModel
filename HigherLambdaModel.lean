/-
# Higher Lambda Model

A Lean 4 formalization of "The Theory of an Arbitrary Higher λ-Model"
by Daniel O. Martínez-Rivillas and Ruy J.G.B. de Queiroz (arXiv:2111.07092).

This library formalizes:
1. Untyped λ-terms using de Bruijn indices
2. β-reduction and η-reduction
3. Higher βη-conversions using explicit constructive higher cells
4. The weak ω-groupoid structure on λ-terms

The key insight from the paper is that in homotopic λ-models (extensional Kan
complexes), the higher βη-conversions form a weak ω-groupoid structure, just
like identity types in homotopy type theory. The current repository develops
this higher structure internally using explicit βη conversion paths, 2-cells,
3-cells, and higher derivation towers above dimension 3.
-/

import HigherLambdaModel.Basic
