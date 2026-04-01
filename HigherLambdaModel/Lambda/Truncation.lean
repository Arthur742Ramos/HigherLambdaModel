/-
# Higher Connectivity Compatibility Layer

This module re-exports the constructive higher-reflexivity facts used by the
current formalization and connects them with the explicit path model.

Unlike earlier versions, this file does not claim that all higher cells are
propositionally unique. It only states the reflexive higher-cell facts that are
actually established by the current constructive encoding.
-/

import HigherLambdaModel.Lambda.TruncationCore
import HigherLambdaModel.Lambda.NTerms
import HigherLambdaModel.Lambda.ExtensionalKan

namespace HigherLambdaModel.Lambda.Truncation

open Term ExtensionalKan HigherTerms NTerms TruncationCore

/-! ## Re-exported h-level Predicates -/

abbrev IsContractible := TruncationCore.IsContractible
abbrev IsProp := TruncationCore.IsProp
abbrev IsSet := TruncationCore.IsSet
abbrev IsTruncated := TruncationCore.IsTruncated

/-! ## Re-exported Reflexive Higher-Cell Facts -/

/-- The reflexive 2-cell space of an explicit path is inhabited. -/
theorem homotopy2_refl_inhabited {M N : Term} (p : ReductionSeq M N) :
    Nonempty (Homotopy2 p p) :=
  TruncationCore.homotopy2_refl_inhabited p

/-- The reflexive 3-cell space of an explicit 2-cell is inhabited. -/
theorem homotopy3_refl_inhabited {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    Nonempty (HigherTerms.Homotopy3 α α) :=
  TruncationCore.homotopy3_refl_inhabited α

/-- Equality of reduction sequences is a proposition. -/
theorem reduction_seq_is_set (M N : Term) : IsSet (ReductionSeq M N) :=
  TruncationCore.reductionSeq_is_set M N

/-! ## The Reflexive Tower -/

abbrev ReflexiveLambdaTower := TruncationCore.ReflexiveLambdaTower

/-- The canonical reflexive tower carried by the constructive higher λ-structure. -/
abbrev reflexiveLambdaTower : ReflexiveLambdaTower :=
  TruncationCore.reflexiveLambdaTower

/-! ## Paths Versus Classical βη-Conversion -/

/-- Proposition-level classical equality obtained by truncating explicit paths. -/
def ClassicalEquality (M N : Term) : Prop :=
  Nonempty (ReductionSeq M N)

/-- The truncation map forgetting the explicit path data. -/
def truncate0 {M N : Term} : ReductionSeq M N → (M =_TH N) :=
  ReductionSeq.toBetaEtaConv

/-- Every classical βη-conversion admits an explicit path representative. -/
theorem truncate0_surjective (M N : Term) (h : M =_TH N) :
    ∃ (seq : ReductionSeq M N), truncate0 seq = h :=
  ⟨ReductionSeq.ofBetaEtaConv h, ReductionSeq.toBetaEtaConv_ofBetaEtaConv h⟩

/-- Explicit paths imply proposition-level βη-conversion. -/
theorem classicalEquality_to_TH_lambda_eq {M N : Term} :
    ClassicalEquality M N → (M =_TH N) := by
  intro h
  rcases h with ⟨seq⟩
  exact truncate0 seq

/-- Proposition-level βη-conversion admits an explicit path representative. -/
theorem TH_lambda_eq_to_classicalEquality {M N : Term} :
    (M =_TH N) → ClassicalEquality M N := by
  intro h
  rcases truncate0_surjective M N h with ⟨seq, _⟩
  exact ⟨seq⟩

/-- Classical βη-equality is exactly the proposition-level truncation of explicit paths. -/
theorem TH_lambda_eq_is_0_truncation (M N : Term) :
    (M =_TH N) ↔ ClassicalEquality M N := by
  constructor
  · exact TH_lambda_eq_to_classicalEquality
  · exact classicalEquality_to_TH_lambda_eq

/-! ## Semantic Consequences -/

/-- An explicit path forces equality in every extensional Kan complex. -/
theorem connected_implies_equal (K : ExtensionalKanComplex) (M N : Term)
    (seq : ReductionSeq M N) : (M =ₖ[K] N) := by
  intro ρ
  exact ExtensionalKan.reductionSeq_sound K seq ρ

/-- Every reduction sequence admits its reflexive 2-cell. -/
def reduction_sequence_self_homotopy (M N : Term) (p : ReductionSeq M N) :
    Homotopy2 p p :=
  TruncationCore.reduction_sequence_self_homotopy M N p

/-- Every 2-cell admits its reflexive 3-cell. -/
def homotopy_self_coherence {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) : HigherTerms.Homotopy3 α α :=
  TruncationCore.homotopy_self_coherence α

/-- Truncating an explicit path preserves semantic soundness. -/
theorem truncation_preserves_soundness (K : ExtensionalKanComplex)
    (M N : Term) (seq : ReductionSeq M N) :
    M =ₖ[K] N :=
  connected_implies_equal K M N seq

end HigherLambdaModel.Lambda.Truncation
