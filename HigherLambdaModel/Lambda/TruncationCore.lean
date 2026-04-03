/-
# Core Higher Connectivity Data

This module records the low-dimensional connectivity facts that follow from the
constructive higher-cell encoding used in the repository.

The current encoding provides explicit 2-cells and 3-cells, so the main facts we
prove are that these higher cells are inhabited for fixed boundaries. We keep the
generic h-level predicates available, but we no longer claim global
contractibility of the higher-cell spaces.
-/

import HigherLambdaModel.Lambda.Coherence
import HigherLambdaModel.Lambda.NTerms

namespace HigherLambdaModel.Lambda.TruncationCore

open Term HigherTerms

/-! ## Truncation Levels (h-levels) -/

/-- A type is contractible if it has a center and every point equals it. -/
def IsContractible (X : Sort u) : Prop :=
  ∃ (center : X), ∀ (x : X), center = x

/-- A type is a proposition if any two of its elements are equal. -/
def IsProp (X : Sort u) : Prop :=
  ∀ (x y : X), x = y

/-- A type is a set if each of its identity types is a proposition. -/
def IsSet (X : Sort u) : Prop :=
  ∀ (x y : X) (p q : x = y), p = q

/-- Recursive truncation levels indexed by natural numbers.

`0` means contractible, `1` means proposition, `2` means set, and so on. -/
def IsTruncated : Nat → Sort _ → Prop
  | 0, X => IsContractible X
  | n + 1, X => ∀ (x y : X), IsTruncated n (x = y)

/-! ## Basic Properties -/

/-- Contractible types are propositions. -/
theorem contractible_is_prop {X : Sort u} (h : IsContractible X) : IsProp X := by
  intro x y
  obtain ⟨center, h_center⟩ := h
  calc
    x = center := (h_center x).symm
    _ = y := h_center y

/-- Propositions are sets. -/
theorem prop_is_set {X : Sort u} (_h : IsProp X) : IsSet X := by
  intro x y p q
  exact Subsingleton.elim p q

/-- Equality in a contractible type is contractible. -/
theorem equality_of_contractible_is_contractible {X : Sort u}
    (h : IsContractible X) (x y : X) : IsContractible (x = y) := by
  refine ⟨contractible_is_prop h x y, ?_⟩
  intro p
  exact Subsingleton.elim _ _

/-! ## Low-Dimensional Reflexivity of Higher λ-Cells -/

/-- Equality of explicit reduction sequences is a proposition. -/
theorem reductionSeq_is_set (M N : Term) : IsSet (ReductionSeq M N) := by
  intro p q hp hq
  exact Subsingleton.elim hp hq

/-- Every explicit path has its reflexive 2-cell. -/
def homotopy2_refl {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 p p :=
  Homotopy2.refl p

/-- Every explicit 2-cell has its reflexive 3-cell. -/
def homotopy3_refl {M N : Term} {p q : ReductionSeq M N}
    (α : HigherTerms.Homotopy2 p q) :
    HigherTerms.Homotopy3 α α :=
  HigherTerms.Homotopy3.refl α

/-- Every explicit path has an inhabited reflexive 2-cell space. -/
theorem homotopy2_refl_inhabited {M N : Term} (p : ReductionSeq M N) :
    Nonempty (Homotopy2 p p) :=
  ⟨homotopy2_refl p⟩

/-- Every explicit 2-cell has an inhabited reflexive 3-cell space. -/
theorem homotopy3_refl_inhabited {M N : Term} {p q : ReductionSeq M N}
    (α : HigherTerms.Homotopy2 p q) :
    Nonempty (HigherTerms.Homotopy3 α α) :=
  ⟨homotopy3_refl α⟩

/-! ## A Packaged Reflexive Tower -/

/-- The low-dimensional higher-cell data carried by the constructive path
model, viewed through the generic simplicial interface. -/
abbrev ReflexiveLambdaTower :=
  HigherLambdaModel.Simplicial.ReflexiveGlobularTower

/-- The proposition-level 0-truncation of the 1-cell space of an
omega-groupoid. -/
def OmegaGroupoid0Truncation
    (G : HigherLambdaModel.Simplicial.OmegaGroupoid) (M N : G.Obj) : Prop :=
  Nonempty (G.Hom M N)

private def higherDerivMap {A B : Type _} (f : A → B) :
    {x y : A} → HigherDeriv x y → HigherDeriv (f x) (f y)
  | _, _, .refl x => HigherDeriv.refl (f x)
  | _, _, .symm h => HigherDeriv.symm (higherDerivMap f h)
  | _, _, .trans h₁ h₂ =>
      HigherDeriv.trans (higherDerivMap f h₁) (higherDerivMap f h₂)

private def liftLambdaCell3 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (η : HigherTerms.Homotopy3 α β) :
    HigherTerms.Cell 3 :=
  ⟨M, N, p, q, α, β, η⟩

private def liftLambdaCell4 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} {η θ : HigherTerms.Homotopy3 α β}
    (ω : HigherTerms.HigherDeriv η θ) :
    HigherTerms.Cell 4 :=
  ⟨liftLambdaCell3 η, liftLambdaCell3 θ, higherDerivMap liftLambdaCell3 ω⟩

private def lambdaRealize4 :
    HigherLambdaModel.Lambda.Coherence.Tower4
      HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid.toReflexiveGlobularTower →
    HigherTerms.Cell 4
  | ⟨M, N, p, q, α, β, η, θ, ω⟩ =>
      liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
        (α := α) (β := β) (η := η) (θ := θ) ω

private def lambdaRealize5 :
    HigherLambdaModel.Lambda.Coherence.Tower5
      HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid.toReflexiveGlobularTower →
    HigherTerms.Cell 5
  | ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ⟩ =>
      ⟨liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
          (α := α) (β := β) (η := η) (θ := θ) ω,
        liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
          (α := α) (β := β) (η := η) (θ := θ) ξ,
        higherDerivMap
          (liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
            (α := α) (β := β) (η := η) (θ := θ))
          μ⟩

/-- The explicit higher λ-conversion tower is admissible for the generic
coherence theorem. -/
def lambdaAdmissibleHigherLambdaModel :
    HigherLambdaModel.Lambda.Coherence.AdmissibleHigherLambdaModel where
  tower := HigherLambdaModel.Lambda.NTerms.lambdaTower
  omegaGroupoid := HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid
  cell0Equiv := HigherLambdaModel.Lambda.Coherence.SortEquiv.refl _
  cell1Equiv := HigherLambdaModel.Lambda.Coherence.SortEquiv.refl _
  cell2Equiv := HigherLambdaModel.Lambda.Coherence.SortEquiv.refl _
  cell3Equiv := HigherLambdaModel.Lambda.Coherence.SortEquiv.refl _
  realize4 := lambdaRealize4
  realize5 := lambdaRealize5

/-- The generic coherence theorem specialized to the constructive higher
λ-conversion tower. -/
def lambdaHigherConversionCoherence :
    HigherLambdaModel.Lambda.Coherence.HigherConversionCoherence
      lambdaAdmissibleHigherLambdaModel :=
  HigherLambdaModel.Lambda.Coherence.higherConversionCoherenceData
    lambdaAdmissibleHigherLambdaModel

/-- The constructive higher λ-conversion tower satisfies the generic coherence
theorem over the canonical omega-groupoid API. -/
theorem lambda_higher_conversions_form_omegaGroupoid :
    Nonempty
      (HigherLambdaModel.Lambda.Coherence.HigherConversionCoherence
        lambdaAdmissibleHigherLambdaModel) :=
  HigherLambdaModel.Lambda.Coherence.higherConversions_form_omegaGroupoid
    lambdaAdmissibleHigherLambdaModel

/-- The canonical higher-cell data coming from λ-terms and explicit paths. -/
def reflexiveLambdaTower : ReflexiveLambdaTower :=
  HigherLambdaModel.Lambda.Coherence.realizedTower lambdaAdmissibleHigherLambdaModel

/-- The generic coherence theorem recovers the canonical reflexive lambda
tower obtained directly from `lambdaOmegaGroupoid`. -/
theorem lambdaHigherConversionCoherence_realizedTower :
    HigherLambdaModel.Lambda.Coherence.realizedTower
      lambdaAdmissibleHigherLambdaModel = reflexiveLambdaTower :=
  rfl

/-! ## Consequences -/

/-- Every reduction sequence admits a reflexive 2-cell. -/
def reduction_sequence_self_homotopy (M N : Term) (p : ReductionSeq M N) :
    Homotopy2 p p :=
  homotopy2_refl p

/-- Every 2-cell admits a reflexive 3-cell. -/
def homotopy_self_coherence {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) : HigherTerms.Homotopy3 α α :=
  homotopy3_refl α

end HigherLambdaModel.Lambda.TruncationCore
