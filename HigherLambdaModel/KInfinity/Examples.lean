import HigherLambdaModel.KInfinity.Properties
import HigherLambdaModel.Lambda.Truncation

/-!
# Non-trivial Higher-Conversion Examples

This module closes Issue 7 from the repository backlog by collecting a small
suite of concrete higher-conversion witnesses built from explicit λ-terms.

The examples focus on:

- a confluence diamond for the duplicated identity term,
- concrete associator and triangle-style coherence witnesses,
- an explicit inequality between two parallel 2-cells,
- compatibility of the explicit path presentation with the ordinary
  proposition-level theory `TH_λ=`,
- and the already formalized separation of the chosen β/η points in `K∞`.
-/

namespace HigherLambdaModel.KInfinity

open HigherLambdaModel.Lambda
open HigherLambdaModel.Lambda.HigherTerms
open HigherLambdaModel.Lambda.NTerms
open HigherLambdaModel.Lambda.Coherence
open HigherLambdaModel.Lambda.Truncation
open HigherLambdaModel.Lambda.TruncationCore
open Term

/-! ## Concrete 1-Cells -/

/-- The duplicated identity application `((I I) (I I))`. -/
def duplicatedIdentity : Term := (Term.I @ Term.I) @ (Term.I @ Term.I)

/-- Any application of the identity combinator contracts in one β-step. -/
def betaIdentity (M : Term) : ReductionSeq (Term.I @ M) M :=
  ReductionSeq.single (BetaEtaStep.beta (BetaStep.beta (var 0) M))

/-- Reduce the left copy of `I I` inside `((I I) (I I))`. -/
def duplicatedIdentity_leftEdge :
    ReductionSeq duplicatedIdentity (Term.I @ (Term.I @ Term.I)) :=
  ReductionSeq.single (BetaEtaStep.beta (BetaStep.appL (BetaStep.beta (var 0) Term.I)))

/-- Reduce the right copy of `I I` inside `((I I) (I I))`. -/
def duplicatedIdentity_rightEdge :
    ReductionSeq duplicatedIdentity ((Term.I @ Term.I) @ Term.I) :=
  ReductionSeq.single (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta (var 0) Term.I)))

/-- After the left inner reduction, contract the remaining argument redex. -/
def duplicatedIdentity_reduceArg :
    ReductionSeq (Term.I @ (Term.I @ Term.I)) (Term.I @ Term.I) :=
  ReductionSeq.single (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta (var 0) Term.I)))

/-- After the right inner reduction, contract the remaining function redex. -/
def duplicatedIdentity_reduceFun :
    ReductionSeq ((Term.I @ Term.I) @ Term.I) (Term.I @ Term.I) :=
  ReductionSeq.single (BetaEtaStep.beta (BetaStep.appL (BetaStep.beta (var 0) Term.I)))

/-- The left-then-right concrete reduction sequence from `((I I) (I I))` to `I`. -/
def duplicatedIdentity_leftPath :
    ReductionSeq duplicatedIdentity Term.I :=
  ReductionSeq.concat duplicatedIdentity_leftEdge
    (ReductionSeq.concat duplicatedIdentity_reduceArg (betaIdentity Term.I))

/-- The right-then-left concrete reduction sequence from `((I I) (I I))` to `I`. -/
def duplicatedIdentity_rightPath :
    ReductionSeq duplicatedIdentity Term.I :=
  ReductionSeq.concat duplicatedIdentity_rightEdge
    (ReductionSeq.concat duplicatedIdentity_reduceFun (betaIdentity Term.I))

/-- A left-associated parenthesization of the left-then-right reduction. -/
def duplicatedIdentity_leftPath_assoc :
    ReductionSeq duplicatedIdentity Term.I :=
  ReductionSeq.concat
    (ReductionSeq.concat duplicatedIdentity_leftEdge duplicatedIdentity_reduceArg)
    (betaIdentity Term.I)

/-! ## Concrete 2-Cell and 3-Cell Examples -/

/-- The confluence diamond between the two reduction orders for `((I I) (I I))`. -/
def duplicatedIdentity_diamond :
    Homotopy2 duplicatedIdentity_leftPath duplicatedIdentity_rightPath :=
  Homotopy2.ofDiamond duplicatedIdentity_leftEdge duplicatedIdentity_rightEdge
    (ReductionSeq.concat duplicatedIdentity_reduceArg (betaIdentity Term.I))
    (ReductionSeq.concat duplicatedIdentity_reduceFun (betaIdentity Term.I))

/-- The associator specialized to the concrete left-then-right reduction. -/
def duplicatedIdentity_associator :
    Homotopy2 duplicatedIdentity_leftPath_assoc duplicatedIdentity_leftPath :=
  Coherence.associator
    duplicatedIdentity_leftEdge duplicatedIdentity_reduceArg (betaIdentity Term.I)

/-- Left whiskering preserves a reflexive 2-cell on the concrete duplicated-identity example. -/
def duplicatedIdentity_whiskerLeftRefl :
    Homotopy3
      (Coherence.whiskerLeft
        duplicatedIdentity_leftEdge (Homotopy2.refl duplicatedIdentity_reduceArg))
      (Homotopy2.refl
        (ReductionSeq.concat duplicatedIdentity_leftEdge duplicatedIdentity_reduceArg)) :=
  whiskerLeft_refl duplicatedIdentity_leftEdge duplicatedIdentity_reduceArg

/-- Triangle coherence specialized to the first two steps of the duplicated-identity reduction. -/
def duplicatedIdentity_triangle :
    Homotopy3
      (Homotopy2.trans
        (Coherence.associator
          duplicatedIdentity_leftEdge (ReductionSeq.refl _) duplicatedIdentity_reduceArg)
        (Coherence.whiskerLeft
          duplicatedIdentity_leftEdge
          (Coherence.leftUnitor duplicatedIdentity_reduceArg)))
      (Coherence.whiskerRight
        (Coherence.rightUnitor duplicatedIdentity_leftEdge) duplicatedIdentity_reduceArg) :=
  triangle duplicatedIdentity_leftEdge duplicatedIdentity_reduceArg

/-! ## Distinct Parallel Higher Conversions -/

/-- A second 2-cell with the same boundary as `duplicatedIdentity_diamond`,
obtained by postcomposing with a reflexive 2-cell. -/
def duplicatedIdentity_diamond_then_refl :
    Homotopy2 duplicatedIdentity_leftPath duplicatedIdentity_rightPath :=
  Homotopy2.trans duplicatedIdentity_diamond (Homotopy2.refl duplicatedIdentity_rightPath)

/-- The concrete diamond 2-cell is not definitionally equal to the one obtained
by postcomposing it with reflexivity. -/
theorem duplicatedIdentity_parallel_2cells_ne :
    duplicatedIdentity_diamond ≠ duplicatedIdentity_diamond_then_refl := by
  intro h
  have hderiv :
      Homotopy2Deriv.diamond
          duplicatedIdentity_leftEdge
          duplicatedIdentity_rightEdge
          (ReductionSeq.concat duplicatedIdentity_reduceArg (betaIdentity Term.I))
          (ReductionSeq.concat duplicatedIdentity_reduceFun (betaIdentity Term.I))
        =
      Homotopy2Deriv.trans
        (Homotopy2Deriv.diamond
          duplicatedIdentity_leftEdge
          duplicatedIdentity_rightEdge
          (ReductionSeq.concat duplicatedIdentity_reduceArg (betaIdentity Term.I))
          (ReductionSeq.concat duplicatedIdentity_reduceFun (betaIdentity Term.I)))
        (Homotopy2Deriv.refl duplicatedIdentity_rightPath) := by
    simpa [duplicatedIdentity_diamond, duplicatedIdentity_diamond_then_refl,
      Homotopy2.ofDiamond, Homotopy2.trans, Homotopy2.refl] using
      congrArg Homotopy2.deriv h
  cases hderiv

/-! ## Compatibility with Ordinary Truncation -/

/-- A concrete Church-numeral β-path used to compare the higher and ordinary theories. -/
def churchOneIdentityPath : ReductionSeq (Term.I @ Term.one) Term.one :=
  betaIdentity Term.one

/-- The generic 0-truncation of the lambda omega-groupoid contains the concrete
Church-numeral identity reduction. -/
theorem churchOne_in_0truncation :
    OmegaGroupoid0Truncation lambdaOmegaGroupoid (Term.I @ Term.one) Term.one := by
  exact ⟨churchOneIdentityPath⟩

/-- Passing to ordinary `TH_λ=` recovers the expected βη-equality. -/
theorem churchOne_truncates_to_TH :
    (Term.I @ Term.one) =_TH Term.one := by
  exact (lambda_generic_coherence_0_truncation (Term.I @ Term.one) Term.one).mp
    churchOne_in_0truncation

/-- The two explicit reduction paths through the duplicated identity collapse to
the same proposition-level βη-equality after truncation. -/
theorem duplicatedIdentity_path_truncations_agree :
    truncate0 duplicatedIdentity_leftPath = truncate0 duplicatedIdentity_rightPath := by
  exact Subsingleton.elim _ _

/-! ## Existing `K∞` Separation Example -/

/-- The chosen β- and η-side points of Example 4.2 remain distinct in `K∞`. -/
theorem beta_eta_points_distinct_in_KInfinity :
    interp1Beta ≠ interp1Eta :=
  example_4_2

/-- The chosen β- and η-side points of Example 4.2 admit no 1-cell in the
canonical `K∞` omega-groupoid. -/
theorem beta_eta_points_disconnected_in_KInfinity :
    ¬ Nonempty (KInfinityPath interp1Beta interp1Eta) :=
  example_4_2_not_connected

/-- Consequently the chosen β- and η-side points of Example 4.2 admit no
parallel 2-cell in the canonical `K∞` omega-groupoid. -/
theorem beta_eta_points_no_2cell_in_KInfinity
    {p q : KInfinityPath interp1Beta interp1Eta} :
    ¬ Nonempty (KInfinityPath2 p q) := by
  intro h
  rcases h with ⟨α⟩
  exact example_4_2_no_path2 α

/-- Consequently the chosen β- and η-side points of Example 4.2 admit no
parallel 3-cell in the canonical `K∞` omega-groupoid. -/
theorem beta_eta_points_no_3cell_in_KInfinity
    {p q : KInfinityPath interp1Beta interp1Eta}
    {α β : KInfinityPath2 p q} :
    ¬ Nonempty (KInfinityPath3 α β) := by
  intro h
  rcases h with ⟨η⟩
  exact example_4_2_no_path3 η

/-- Consequently the chosen β- and η-side points of Example 4.2 admit no
parallel 4-cell in the canonical `K∞` omega-groupoid. -/
theorem beta_eta_points_no_4cell_in_KInfinity
    {p q : KInfinityPath interp1Beta interp1Eta}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β} :
    ¬ Nonempty (KInfinityPath4 η θ) := by
  intro h
  rcases h with ⟨ω⟩
  exact example_4_2_no_path4 ω

/-- Consequently the chosen β- and η-side points of Example 4.2 admit no
parallel 5-cell in the canonical `K∞` omega-groupoid. -/
theorem beta_eta_points_no_5cell_in_KInfinity
    {p q : KInfinityPath interp1Beta interp1Eta}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    {ω ξ : KInfinityPath4 η θ} :
    ¬ Nonempty (KInfinityPath5 ω ξ) := by
  intro h
  rcases h with ⟨μ⟩
  exact example_4_2_no_path5 μ

/-- The stronger all-dimensional version of Example 4.2 for the recursively
completed `K∞` tower: from dimension `5` onward, there is no packed higher cell
whose 0-source/0-target boundary is the chosen β/η pair. -/
theorem beta_eta_points_no_recursive_higher_cell_in_KInfinity
    (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = interp1Beta ∧
          kInfinityTowerTargetObj x = interp1Eta} :=
  example_4_2_no_recursive_higher_cell_nonempty n

end HigherLambdaModel.KInfinity
