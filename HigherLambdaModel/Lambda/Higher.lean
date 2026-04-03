/-
# Higher Conversions Compatibility Layer

This module used to model higher λ-conversions by postulating that β/η steps
induce Lean equality proofs. That approach introduced auxiliary axioms and did
not retain explicit higher-cell data.

The current version is a compatibility facade over the explicit higher
conversion objects defined in `HigherTerms.lean`.
-/

import HigherLambdaModel.Lambda.Coherence

namespace HigherLambdaModel.Lambda

open Term
open HigherLambdaModel.Lambda.HigherTerms

/-! ## Paths and Higher Cells -/

/-- A path between terms is represented by an explicit βη-reduction sequence. -/
abbrev TermPath (M N : Term) := ReductionSeq M N

/-- A single β-step packaged as an explicit path. -/
def betaPath {M N : Term} (h : BetaStep M N) : TermPath M N :=
  ReductionSeq.single (BetaEtaStep.beta h)

/-- A single η-step packaged as an explicit path. -/
def etaPath {M N : Term} (h : EtaStep M N) : TermPath M N :=
  ReductionSeq.single (BetaEtaStep.eta h)

/-- A single βη-step packaged as an explicit path. -/
def betaEtaStepPath {M N : Term} (h : BetaEtaStep M N) : TermPath M N :=
  ReductionSeq.single h

/-- Legacy name for explicit 1-cells. -/
abbrev LambdaPath (M N : Term) := ReductionSeq M N

/-- Canonical weak omega-groupoid interface on λ-terms. -/
abbrev LambdaOmegaGroupoid :=
  Coherence.LambdaOmegaGroupoid

/-- Re-export of the canonical lambda omega-groupoid structure. -/
abbrev lambdaOmegaGroupoid : LambdaOmegaGroupoid :=
  Coherence.lambdaOmegaGroupoid

namespace LambdaPath

/-- Identity path. -/
def refl (M : Term) : LambdaPath M M := lambdaOmegaGroupoid.id M

/-- Composition of paths. -/
def trans {M N P : Term} (p : LambdaPath M N) (q : LambdaPath N P) : LambdaPath M P :=
  lambdaOmegaGroupoid.comp p q

/-- Symmetry uses the inverse operation supplied by `HigherTerms`. -/
def symm {M N : Term} (p : LambdaPath M N) : LambdaPath N M :=
  lambdaOmegaGroupoid.inv p

/-- A single βη-step as a path. -/
def step {M N : Term} (h : BetaEtaStep M N) : LambdaPath M N :=
  ReductionSeq.single h

end LambdaPath

/-- Legacy name for explicit 2-cells. -/
abbrev Lambda2Cell {M N : Term} (p q : LambdaPath M N) := Homotopy2 p q

namespace Lambda2Cell

/-- Identity 2-cell. -/
def refl {M N : Term} (p : LambdaPath M N) : Lambda2Cell p p :=
  lambdaOmegaGroupoid.refl2 p

/-- Vertical composition of 2-cells. -/
def trans {M N : Term} {p q r : LambdaPath M N}
    (α : Lambda2Cell p q) (β : Lambda2Cell q r) : Lambda2Cell p r :=
  lambdaOmegaGroupoid.trans2 α β

/-- Symmetry of 2-cells. -/
def symm {M N : Term} {p q : LambdaPath M N} (α : Lambda2Cell p q) : Lambda2Cell q p :=
  lambdaOmegaGroupoid.symm2 α

end Lambda2Cell

/-- Legacy name for explicit 3-cells. -/
abbrev Lambda3Cell {M N : Term} {p q : LambdaPath M N}
    (α β : Lambda2Cell p q) := HigherTerms.Homotopy3 α β

namespace Lambda3Cell

/-- Identity 3-cell. -/
def refl {M N : Term} {p q : LambdaPath M N}
    (α : Lambda2Cell p q) : Lambda3Cell α α :=
  HigherTerms.Homotopy3.refl α

end Lambda3Cell

/-! ## Groupoid-Style Operations -/

/-- Right inverse law up to homotopy. -/
def path_inv_right {M N : Term} (p : LambdaPath M N) :
    Lambda2Cell (LambdaPath.trans p (LambdaPath.symm p)) (LambdaPath.refl M) :=
  lambdaOmegaGroupoid.inv_right p

/-- Left inverse law up to homotopy. -/
def path_inv_left {M N : Term} (p : LambdaPath M N) :
    Lambda2Cell (LambdaPath.trans (LambdaPath.symm p) p) (LambdaPath.refl N) :=
  lambdaOmegaGroupoid.inv_left p

/-- Associativity of path composition up to homotopy. -/
def path_assoc {M N P Q : Term}
    (p : LambdaPath M N) (q : LambdaPath N P) (r : LambdaPath P Q) :
    Lambda2Cell (LambdaPath.trans (LambdaPath.trans p q) r)
                (LambdaPath.trans p (LambdaPath.trans q r)) :=
  lambdaOmegaGroupoid.associator p q r

/-! ## Legacy Exports -/

/-- Extensional equality: equal behavior on all arguments. -/
def ExtEqual (M N : Term) : Prop :=
  ∀ (P : Term), BetaEtaConv (app M P) (app N P)

/-- Weak ω-groupoid data packaged using explicit reduction sequences. -/
abbrev lambdaOmegaGroupoidData : LambdaOmegaGroupoidData :=
  lambdaOmegaGroupoid.toOmegaGroupoidData

/-! ## Example -/

/-- The term `(λx.x) (λy.y)` β-reduces to `λy.y` in one step. -/
def example_term : Term := Term.I @ Term.I

/-- Example witness of the single β-step from `example_term` to `Term.I`. -/
example : BetaStep example_term Term.I :=
  BetaStep.beta (var 0) Term.I

end HigherLambdaModel.Lambda
