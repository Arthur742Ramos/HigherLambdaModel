/-
# Higher λ-Model Formalization: Main Results

This file summarizes the main results from our formalization of
"The Theory of an Arbitrary Higher λ-Model" (arXiv:2111.07092).

## Summary of Formalization

### 1. Lambda Calculus Infrastructure (Lambda/Term.lean, Lambda/Reduction.lean)
- De Bruijn representation of λ-terms
- β-reduction: (λM)N →β M[N/x]
- η-reduction: λx.Mx →η M (when x ∉ FV(M))
- Combined βη-reduction and conversion

### 2. Higher Structure (Lambda/HigherTerms.lean)
- Explicit reduction sequences as 1-cells
- Explicit common-extension witnesses as 2-cells
- Explicit 3-cells between parallel 2-cells
- Identity-type higher cells above dimension 3
- Weak ω-groupoid structure on λ-terms

### 3. Extensional Kan Complexes (Lambda/ExtensionalKan.lean)
- Reflexive Kan Complex: (K, F, G, η) where η : FG ≅ 1
- Extensional Kan Complex: adds ε : 1 ≅ GF
- Interpretation ⟦-⟧ρ : Term → K.Obj
- β-soundness: ⟦(λM)N⟧ = ⟦M[N]⟧
- η-soundness: ⟦λx.Mx⟧ = ⟦M⟧ (when x ∉ FV(M))
- HoTFT: Intersection of all extensional Kan complex theories
- Proof-relevant semantic 1-conversions: `Theory1` and `HoTFT1`, with explicit path composition and inversion via horn fillers
- Proof-relevant semantic 2-conversions: `Theory2` and `HoTFT2`, carried by actual simplicial 2-cells, with structural symmetry, left/right whiskering, associators, and unitors
- Proof-relevant semantic 3-conversions: `Theory3` and `HoTFT3`, carried by actual simplicial 3-cells, with reflexivity, symmetry, vertical composition, equality transport, and interchange formalized
- Initial proof-relevant semantic 4-conversions: `Theory4` and `HoTFT4`, carried by actual simplicial 4-cells, with reflexivity and equality transport already formalized
- Packaging of extensional Kan complexes as `HomotopicLambdaModel`s

### 3a. Homotopy Domain Order Layer (Lambda/HomotopyOrder.lean)
- Homotopy partial orders (Definition 2.3)
- Complete homotopy partial orders (Definition 2.4)
- Continuous maps and CHP O morphisms (Definitions 2.5-2.6)

### 4. N-Terms and N-Conversions (Lambda/NTerms.lean)
- Σ₀ = λ-terms (0-conversions)
- Σ₁ = βη-reduction sequences (1-conversions)
- Σ₂ = homotopies between parallel sequences (2-conversions)
- Σₙ (n ≥ 3) = recursively generated higher cells
- Πₙ = n-terms (computational witnesses for n-conversions)
- Embedding: Πₙ ⊆ Σₙ (Proposition 3.4)
- Main Theorem: TH_λ= ⊆ HoTFT
- Explicit `Homotopy2` cells now interpret directly into semantic `HoTFT2` cells carried by the structural HoTFT 1-cells of their boundaries
- Reflexive, equality-generated, symmetric, vertically composable, and interchange 3-cells over those semantic `HoTFT2` boundaries now land in an actual simplicial `HoTFT3` layer
- A supported explicit syntactic 3-cell fragment `StructuralHomotopy3`, now closed under symmetry, vertical composition, reflexive left/right whiskering, left-whiskering transitivity, left-whiskering symmetry, and interchange, maps directly into that `HoTFT3` layer
- Reflexive 4-cells over the current interpreted 3-cell fragment now land in an actual simplicial `HoTFT4` layer

## Key Results

**Theorem (β-soundness)**: In any extensional Kan complex K,
  ⟦(λM)N⟧ρ = ⟦M[N/x]⟧ρ

**Theorem (η-soundness)**: In any extensional Kan complex K, if x ∉ FV(M),
  ⟦λx.Mx⟧ρ = ⟦M⟧ρ

**Theorem (TH_λ= ⊆ HoTFT)**: If M =βη N in the classical λ-theory,
  then M = N in every extensional Kan complex.

## Mathematical Significance

The paper shows that:
1. The higher structure of λ-calculus (n-conversions) emerges naturally
2. This structure forms a weak ω-groupoid
3. N-terms provide computational witnesses for n-conversions
4. Classical βη-equality embeds into the homotopic theory

This connects untyped λ-calculus to homotopy type theory, showing that
even the "untyped" setting has rich higher-categorical structure.
-/

import HigherLambdaModel.Lambda

namespace HigherLambdaModel

open Lambda Lambda.ExtensionalKan Lambda.NTerms Lambda.HigherTerms

/-! ## Main Results -/

-- Re-export the key theorem names through the namespace opened above.

/-! ## Example: The Identity Function

Let's verify that the identity combinator behaves as expected. -/

-- I = λx.x reduces any term M to itself
example (M : Term) : Term.app Term.I M →*βη M :=
  HigherLambdaModel.Lambda.BetaEtaClosure.single
    (HigherLambdaModel.Lambda.BetaEtaStep.beta
      (HigherLambdaModel.Lambda.BetaStep.beta (Term.var 0) M))

/-! ## The Paper's Main Insight

The key insight of the paper is that in any **extensional Kan complex**
(the categorical structure underlying homotopic λ-models), the higher
βη-conversions form a coherent algebraic structure - a weak ω-groupoid.

This means:
1. Terms are 0-cells
2. Reduction sequences are 1-cells (explicit paths, not mere existence)
3. Homotopies between sequences are 2-cells
4. Higher cells satisfy coherence conditions

The paper proves that Πₙ ⊆ Σₙ, meaning every "n-term" (computational witness)
corresponds to an "n-conversion" (abstract equivalence). This is formalized
in our `pi_subset_sigma` and `TH_lambda_eq_subset_HoTFT` theorems. -/

end HigherLambdaModel
