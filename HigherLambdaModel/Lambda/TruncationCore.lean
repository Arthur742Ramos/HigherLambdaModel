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

private def liftLambdaCell5 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} {η θ : HigherTerms.Homotopy3 α β}
    {ω ξ : HigherTerms.HigherDeriv η θ} (μ : HigherTerms.HigherDeriv ω ξ) :
    HigherTerms.Cell 5 :=
  ⟨liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
      (α := α) (β := β) (η := η) (θ := θ) ω,
    liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
      (α := α) (β := β) (η := η) (θ := θ) ξ,
    higherDerivMap
      (liftLambdaCell4 (M := M) (N := N) (p := p) (q := q)
        (α := α) (β := β) (η := η) (θ := θ))
      μ⟩

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

private def lambdaRealize6 :
    HigherLambdaModel.Lambda.Coherence.Tower6
      HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid.toReflexiveGlobularTower →
    HigherTerms.Cell 6
  | ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ, ν, tau⟩ =>
      ⟨liftLambdaCell5 (M := M) (N := N) (p := p) (q := q)
          (α := α) (β := β) (η := η) (θ := θ) (ω := ω) (ξ := ξ) μ,
        liftLambdaCell5 (M := M) (N := N) (p := p) (q := q)
          (α := α) (β := β) (η := η) (θ := θ) (ω := ω) (ξ := ξ) ν,
        higherDerivMap
          (liftLambdaCell5 (M := M) (N := N) (p := p) (q := q)
            (α := α) (β := β) (η := η) (θ := θ) (ω := ω) (ξ := ξ))
          tau⟩

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
  realize6 := lambdaRealize6

private abbrev lambdaOmegaReflexiveTower : ReflexiveLambdaTower :=
  HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid.toReflexiveGlobularTower

/-- The shared all-dimensional omega tower induced directly from the canonical
lambda omega-groupoid. -/
def lambdaOmegaTower : HigherLambdaModel.Simplicial.GlobularTower :=
  HigherLambdaModel.Lambda.Coherence.omegaGroupoidTower
    HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid

/-- The shared all-dimensional constructive omega tower induced directly from the
canonical lambda omega-groupoid by recursive `HigherDeriv` completion above the
explicit 6-cell core. -/
def lambdaOmegaConstructiveTower : HigherLambdaModel.Simplicial.GlobularTower :=
  HigherLambdaModel.Lambda.Coherence.omegaGroupoidHigherTower
    HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid

private abbrev lambdaOmegaConstructiveCell : Nat → Sort _ :=
  HigherLambdaModel.Lambda.Coherence.recursiveHigherCell
    HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid.toReflexiveGlobularTower

private def lambdaOmegaCell0Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (lambdaOmegaTower.Cell 0)
      (HigherLambdaModel.Lambda.Coherence.Tower0 lambdaOmegaReflexiveTower) where
  toFun := fun x => x.down
  invFun := fun x => ⟨x⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl

private def lambdaOmegaCell1Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (lambdaOmegaTower.Cell 1)
      (HigherLambdaModel.Lambda.Coherence.Tower1 lambdaOmegaReflexiveTower) where
  toFun := fun ⟨M, N, p⟩ => ⟨M.down, N.down, p.down⟩
  invFun := fun ⟨M, N, p⟩ => ⟨⟨M⟩, ⟨N⟩, ⟨p⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk M rest =>
        cases rest with
        | mk N p =>
            cases M
            cases N
            cases p
            rfl
  right_inv := by
    intro x
    cases x
    rfl

private def lambdaOmegaCell2Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (lambdaOmegaTower.Cell 2)
      (HigherLambdaModel.Lambda.Coherence.Tower2 lambdaOmegaReflexiveTower) where
  toFun := fun ⟨M, N, p, q, α⟩ => ⟨M.down, N.down, p.down, q.down, α.down⟩
  invFun := fun ⟨M, N, p, q, α⟩ => ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk M rest =>
        cases rest with
        | mk N rest =>
            cases rest with
            | mk p rest =>
                cases rest with
                | mk q α =>
                    cases M
                    cases N
                    cases p
                    cases q
                    cases α
                    rfl
  right_inv := by
    intro x
    cases x
    rfl

private def lambdaOmegaCell3Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (lambdaOmegaTower.Cell 3)
      (HigherLambdaModel.Lambda.Coherence.Tower3 lambdaOmegaReflexiveTower) where
  toFun := fun ⟨M, N, p, q, α, β, η⟩ =>
    ⟨M.down, N.down, p.down, q.down, α.down, β.down, η.down⟩
  invFun := fun ⟨M, N, p, q, α, β, η⟩ =>
    ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk M rest =>
        cases rest with
        | mk N rest =>
            cases rest with
            | mk p rest =>
                cases rest with
                | mk q rest =>
                    cases rest with
                    | mk α rest =>
                        cases rest with
                        | mk β η =>
                            cases M
                            cases N
                            cases p
                            cases q
                            cases α
                            cases β
                            cases η
                            rfl
  right_inv := by
    intro x
    cases x
    rfl

private def lambdaOmegaRealize4 :
    HigherLambdaModel.Lambda.Coherence.Tower4 lambdaOmegaReflexiveTower →
      lambdaOmegaTower.Cell 4
  | ⟨M, N, p, q, α, β, η, θ, ω⟩ =>
      ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩, ⟨θ⟩, ⟨ω⟩⟩

private def lambdaOmegaRealize5 :
    HigherLambdaModel.Lambda.Coherence.Tower5 lambdaOmegaReflexiveTower →
      lambdaOmegaTower.Cell 5
  | ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ⟩ =>
      ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩, ⟨θ⟩, ⟨ω⟩, ⟨ξ⟩, ⟨μ⟩⟩

private def lambdaOmegaRealize6 :
    HigherLambdaModel.Lambda.Coherence.Tower6 lambdaOmegaReflexiveTower →
      lambdaOmegaTower.Cell 6
  | ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ, ν, tau⟩ =>
      ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩, ⟨θ⟩,
        ⟨ω⟩, ⟨ξ⟩, ⟨μ⟩, ⟨ν⟩, ⟨tau⟩⟩

/-- The constructive omega-groupoid tower on λ-terms realizes into the explicit
recursive higher-conversion tower in every dimension. -/
def lambdaOmegaConstructiveRealize :
    (n : Nat) → lambdaOmegaConstructiveCell n → HigherTerms.Cell n
  | 0, x => x.down
  | 1, ⟨M, N, p⟩ => ⟨M.down, N.down, p.down⟩
  | 2, ⟨M, N, p, q, α⟩ => ⟨M.down, N.down, p.down, q.down, α.down⟩
  | 3, ⟨M, N, p, q, α, β, η⟩ =>
      ⟨M.down, N.down, p.down, q.down, α.down, β.down, η.down⟩
  | 4, ⟨M, N, p, q, α, β, η, θ, ω⟩ =>
      lambdaRealize4 ⟨M.down, N.down, p.down, q.down, α.down, β.down, η.down, θ.down, ω.down⟩
  | 5, ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ⟩ =>
      lambdaRealize5
        ⟨M.down, N.down, p.down, q.down, α.down, β.down, η.down, θ.down, ω.down, ξ.down, μ.down⟩
  | 6, ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ, ν, tau⟩ =>
      lambdaRealize6
        ⟨M.down, N.down, p.down, q.down, α.down, β.down, η.down, θ.down,
          ω.down, ξ.down, μ.down, ν.down, tau.down⟩
  | n + 7, ⟨x, y, h⟩ =>
      ⟨lambdaOmegaConstructiveRealize (n + 6) x,
        lambdaOmegaConstructiveRealize (n + 6) y,
        higherDerivMap (lambdaOmegaConstructiveRealize (n + 6)) h⟩

private theorem lambdaOmegaConstructiveRealize_source_comm :
    ∀ {n : Nat} (x : lambdaOmegaConstructiveCell (n + 1)),
      lambdaOmegaConstructiveRealize n
          (HigherLambdaModel.Lambda.Coherence.recursiveHigherSource
            lambdaOmegaReflexiveTower x) =
        HigherTerms.Cell.source (lambdaOmegaConstructiveRealize (n + 1) x)
  | 0, ⟨_, _, _⟩ => rfl
  | 1, ⟨_, _, _, _, _⟩ => rfl
  | 2, ⟨_, _, _, _, _, _, _⟩ => rfl
  | 3, ⟨_, _, _, _, _, _, _, _, _⟩ => rfl
  | 4, ⟨_, _, _, _, _, _, _, _, _, _, _⟩ => rfl
  | 5, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl
  | _ + 6, ⟨_, _, _⟩ => rfl

private theorem lambdaOmegaConstructiveRealize_target_comm :
    ∀ {n : Nat} (x : lambdaOmegaConstructiveCell (n + 1)),
      lambdaOmegaConstructiveRealize n
          (HigherLambdaModel.Lambda.Coherence.recursiveHigherTarget
            lambdaOmegaReflexiveTower x) =
        HigherTerms.Cell.target (lambdaOmegaConstructiveRealize (n + 1) x)
  | 0, ⟨_, _, _⟩ => rfl
  | 1, ⟨_, _, _, _, _⟩ => rfl
  | 2, ⟨_, _, _, _, _, _, _⟩ => rfl
  | 3, ⟨_, _, _, _, _, _, _, _, _⟩ => rfl
  | 4, ⟨_, _, _, _, _, _, _, _, _, _, _⟩ => rfl
  | 5, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl
  | _ + 6, ⟨_, _, _⟩ => rfl

/-- The shared recursively completed omega-groupoid tower on λ-terms is already
a direct all-dimensional constructive coherence package. -/
def lambdaOmegaConstructiveHigherConversionCoherence :
    HigherLambdaModel.Lambda.Coherence.AllDimensionalHigherConversionCoherence
      lambdaOmegaConstructiveTower
      lambdaOmegaReflexiveTower :=
  HigherLambdaModel.Lambda.Coherence.omegaGroupoidHigherConversionCoherence
    HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid

/-- The explicit higher λ-conversion tower is directly realized by the shared
all-dimensional constructive omega-groupoid tower in every dimension. -/
def lambdaConstructiveHigherConversionCoherence :
    HigherLambdaModel.Lambda.Coherence.AllDimensionalHigherConversionCoherence
      HigherLambdaModel.Lambda.NTerms.lambdaTower
      lambdaOmegaReflexiveTower where
  realize := lambdaOmegaConstructiveRealize
  source_comm := by
    intro n x
    exact lambdaOmegaConstructiveRealize_source_comm x
  target_comm := by
    intro n x
    exact lambdaOmegaConstructiveRealize_target_comm x

/-- The direct all-dimensional constructive coherence package on λ-terms is
inhabited. -/
theorem lambda_constructive_higher_conversions_form_allDimensional_omegaGroupoid :
    Nonempty
      (HigherLambdaModel.Lambda.Coherence.AllDimensionalHigherConversionCoherence
        HigherLambdaModel.Lambda.NTerms.lambdaTower
        lambdaOmegaReflexiveTower) := by
  exact ⟨lambdaConstructiveHigherConversionCoherence⟩

/-- The shared omega-groupoid tower on λ-terms is also admissible for the
generic coherence theorem. This reuses the all-dimensional identity-completion
constructor rather than the explicit recursive `HigherTerms.Cell` tower. -/
def lambdaOmegaAdmissibleHigherLambdaModel :
    HigherLambdaModel.Lambda.Coherence.AdmissibleHigherLambdaModel where
  tower := lambdaOmegaTower
  omegaGroupoid := HigherLambdaModel.Lambda.Coherence.lambdaOmegaGroupoid
  cell0Equiv := lambdaOmegaCell0Equiv
  cell1Equiv := lambdaOmegaCell1Equiv
  cell2Equiv := lambdaOmegaCell2Equiv
  cell3Equiv := lambdaOmegaCell3Equiv
  realize4 := lambdaOmegaRealize4
  realize5 := lambdaOmegaRealize5
  realize6 := lambdaOmegaRealize6

/-- The generic coherence theorem specialized to the shared omega-groupoid tower
on λ-terms. -/
def lambdaOmegaHigherConversionCoherence :
    HigherLambdaModel.Lambda.Coherence.HigherConversionCoherence
      lambdaOmegaAdmissibleHigherLambdaModel :=
  HigherLambdaModel.Lambda.Coherence.higherConversionCoherenceData
    lambdaOmegaAdmissibleHigherLambdaModel

/-- The shared omega-groupoid tower on λ-terms satisfies the generic coherence
theorem as well. -/
theorem lambdaOmega_higher_conversions_form_omegaGroupoid :
    Nonempty
      (HigherLambdaModel.Lambda.Coherence.HigherConversionCoherence
        lambdaOmegaAdmissibleHigherLambdaModel) :=
  HigherLambdaModel.Lambda.Coherence.higherConversions_form_omegaGroupoid
    lambdaOmegaAdmissibleHigherLambdaModel

/-- The explicit higher-cell tower package and the shared omega-groupoid tower
package recover the same low-dimensional reflexive λ-core. -/
theorem lambdaAdmissible_realizedTower_eq_lambdaOmega_realizedTower :
    HigherLambdaModel.Lambda.Coherence.realizedTower
      lambdaAdmissibleHigherLambdaModel =
        HigherLambdaModel.Lambda.Coherence.realizedTower
          lambdaOmegaAdmissibleHigherLambdaModel :=
  rfl

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

/-- The shared omega-groupoid tower package recovers the same reflexive λ-core
obtained directly from `lambdaOmegaGroupoid`. -/
theorem lambdaOmegaHigherConversionCoherence_realizedTower :
    HigherLambdaModel.Lambda.Coherence.realizedTower
      lambdaOmegaAdmissibleHigherLambdaModel = reflexiveLambdaTower := by
  simpa [reflexiveLambdaTower] using
    lambdaAdmissible_realizedTower_eq_lambdaOmega_realizedTower.symm

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
