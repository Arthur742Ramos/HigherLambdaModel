/-
# Lambda Calculus Module

This module aggregates all the λ-calculus definitions:
- Term : Basic untyped λ-terms (de Bruijn representation)
- Reduction : β and η reduction relations
- ChurchRosserProof : β-confluence transferred from Metatheory
- Higher : Higher βη-conversions via computational paths
- HigherTerms : Explicit n-cells and groupoid structure (paper formalization)
- Coherence : Coherence laws for the explicit higher-cell structure
- BetaEtaConfluence : Compatibility layer for explicit common extensions
- NTerms : N-conversions and the tower structure (Section 3)
- TruncationCore : Truncation levels and h-levels (Section 4)
- Truncation : Truncation consequences for the current constructive tower
-/

import HigherLambdaModel.Lambda.Term
import HigherLambdaModel.Lambda.Reduction
import HigherLambdaModel.Lambda.ChurchRosserProof
import HigherLambdaModel.Lambda.Higher
import HigherLambdaModel.Lambda.HigherTerms
import HigherLambdaModel.Lambda.Coherence
import HigherLambdaModel.Lambda.BetaEtaConfluence
import HigherLambdaModel.Lambda.ExtensionalKan
import HigherLambdaModel.Lambda.NTerms
import HigherLambdaModel.Lambda.TruncationCore
import HigherLambdaModel.Lambda.Truncation
import HigherLambdaModel.Lambda.HomotopyOrder
