import HigherLambdaModel.Lambda.ExtensionalKanCore
import HigherLambdaModel.Lambda.ExtensionalKanHigher
import HigherLambdaModel.Lambda.ExtensionalKanStrict

/-!
# Extensional Kan Complexes and Homotopic λ-Models

Umbrella module for the extensional Kan / HoTFT development.

The implementation is split so edits to the higher semantic or strict-filler
layers do not force recompilation of the simplicial/core interpreter layer.
-/
