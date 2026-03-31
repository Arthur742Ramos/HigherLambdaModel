/-
# Core Higher Connectivity Data

This module records the low-dimensional connectivity facts that follow from the
constructive higher-cell encoding used in the repository.

The current encoding provides explicit 2-cells and 3-cells, so the main facts we
prove are that these higher cells are inhabited for fixed boundaries. We keep the
generic h-level predicates available, but we no longer claim global
contractibility of the higher-cell spaces.
-/

import HigherLambdaModel.Lambda.HigherTerms

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

/-- The low-dimensional higher-cell data carried by the constructive path model. -/
structure ReflexiveLambdaTower where
  Cell0 : Type
  Cell1 : Cell0 → Cell0 → Type
  Cell2 : {M N : Cell0} → Cell1 M N → Cell1 M N → Sort _
  Cell3 : {M N : Cell0} → {p q : Cell1 M N} → Cell2 p q → Cell2 p q → Sort _
  cell2_refl : ∀ {M N : Cell0} (p : Cell1 M N), Cell2 p p
  cell3_refl : ∀ {M N : Cell0} {p q : Cell1 M N}
      (α : Cell2 p q), Cell3 α α

/-- The canonical higher-cell data coming from λ-terms and explicit paths. -/
def reflexiveLambdaTower : ReflexiveLambdaTower where
  Cell0 := Term
  Cell1 := ReductionSeq
  Cell2 := @Homotopy2
  Cell3 := @HigherTerms.Homotopy3
  cell2_refl := @homotopy2_refl
  cell3_refl := @homotopy3_refl

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
