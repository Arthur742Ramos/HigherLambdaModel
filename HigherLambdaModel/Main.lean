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
- Homotopies between reduction sequences as 2-cells
- Church-Rosser 2-cells from confluence
- Weak ω-groupoid structure on λ-terms

### 3. Extensional Kan Complexes (Lambda/ExtensionalKan.lean)
- Reflexive Kan Complex: (K, F, G, η) where η : FG ≅ 1
- Extensional Kan Complex: adds ε : 1 ≅ GF
- Interpretation ⟦-⟧ρ : Term → K.Obj
- β-soundness: ⟦(λM)N⟧ = ⟦M[N]⟧
- η-soundness: ⟦λx.Mx⟧ = ⟦M⟧ (when x ∉ FV(M))
- HoTFT: Intersection of all extensional Kan complex theories

### 4. N-Terms and N-Conversions (Lambda/NTerms.lean)
- Σ₀ = λ-terms (0-conversions)
- Σ₁ = βη-reduction sequences (1-conversions)
- Σ₂ = homotopies between parallel sequences (2-conversions)
- Σₙ (n ≥ 3) = trivial in extensional models
- Πₙ = n-terms (computational witnesses for n-conversions)
- Embedding: Πₙ ⊆ Σₙ (Proposition 3.4)
- Main Theorem: TH_λ= ⊆ HoTFT

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

-- Re-export the key theorems

/-- β-reduction is sound in any extensional Kan complex -/
#check @beta_sound

/-- The embedding of classical λ-theory into HoTFT -/
#check @TH_lambda_eq_subset_HoTFT

/-- The embedding of n-terms into n-conversions -/
#check @pi_subset_sigma

/-- The weak ω-groupoid structure on λ-terms -/
#check @lambdaOmegaGroupoidData

/-- The tower of n-conversions -/
#check @lambdaTower

/-! ## Example: The Identity Function

Let's verify that the identity combinator behaves as expected. -/

-- I = λx.x reduces any term M to itself
example (M : Term) : (Term.I @ M) →*βη M :=
  BetaEtaClosure.single (BetaEtaStep.beta (BetaStep.beta (Term.var 0) M))

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
