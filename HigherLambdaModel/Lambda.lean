/-
# Lambda Calculus Module

This module aggregates all the λ-calculus definitions:
- Term : Basic untyped λ-terms (de Bruijn representation)
- Reduction : β and η reduction relations
- Higher : Higher βη-conversions via computational paths
- HigherTerms : Explicit n-cells and groupoid structure (paper formalization)
- NTerms : N-conversions and the tower structure (Section 3)
- TruncationCore : Truncation levels and h-levels (Section 4)
-/

import HigherLambdaModel.Lambda.Term
import HigherLambdaModel.Lambda.Reduction
import HigherLambdaModel.Lambda.Higher
import HigherLambdaModel.Lambda.HigherTerms
import HigherLambdaModel.Lambda.ExtensionalKan
import HigherLambdaModel.Lambda.NTerms
import HigherLambdaModel.Lambda.TruncationCore
