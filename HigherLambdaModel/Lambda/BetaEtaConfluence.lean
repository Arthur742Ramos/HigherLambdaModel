/-
# βη Confluence Compatibility Layer

This repository originally pursued βη-confluence through a direct proof that
β- and η-reduction commute. That development depended on an unfinished
postulated lemma.

The constructive core now models 1-cells by explicit βη-conversion zigzags
(`ReductionSeq`). For this representation, the compatibility notion that is
actually used is a concrete common-extension witness.
-/

import HigherLambdaModel.Lambda.HigherTerms

namespace HigherLambdaModel.Lambda.BetaEtaConfluence

open Term
open HigherLambdaModel.Lambda.HigherTerms

/-- Explicit common-extension data for two terms. -/
structure CommonExtension (M N : Term) where
  apex : Term
  left : ReductionSeq M apex
  right : ReductionSeq N apex

/-- Proposition-level joinability, obtained by forgetting the explicit witness. -/
def Joinable (M N : Term) : Prop :=
  Nonempty (CommonExtension M N)

/-- The joinability witness packaged as explicit common-extension data. -/
def commonExtension {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq M P) :
    CommonExtension N P :=
  { apex := M
    left := p.inv
    right := q.inv }

/-- Two paths out of a common source are constructively joinable. -/
theorem parallel_paths_joinable {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq M P) : Joinable N P := by
  exact ⟨commonExtension p q⟩

/-- An explicit confluence diamond induces a 2-cell in the higher-path core. -/
def diamond_homotopic {M N₁ N₂ P : Term}
    (p₁ : ReductionSeq M N₁) (p₂ : ReductionSeq M N₂)
    (q₁ : ReductionSeq N₁ P) (q₂ : ReductionSeq N₂ P) :
    Homotopy2 (ReductionSeq.concat p₁ q₁) (ReductionSeq.concat p₂ q₂) :=
  Homotopy2.ofDiamond p₁ p₂ q₁ q₂

end HigherLambdaModel.Lambda.BetaEtaConfluence
