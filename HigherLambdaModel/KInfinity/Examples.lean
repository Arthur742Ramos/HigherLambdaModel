import HigherLambdaModel.KInfinity.Properties
import HigherLambdaModel.KInfinity.ContinuousSemantics
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
open HigherLambdaModel.Lambda.HomotopyOrder
open HigherLambdaModel.Domain
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

/-! ## Paper β/η Witness Pattern -/

/-- The open source term `(λz.xz) y` from the paper's β/η nonequivalence
example, in de Bruijn form with free variables `x = var 1` and `y = var 0`. -/
def betaEtaPaperSource : Term :=
  (ƛ ((var 2) @ (var 0))) @ (var 0)

/-- The common target `xy` of the β-side and η-side contractions from
`betaEtaPaperSource`. -/
def betaEtaPaperTarget : Term :=
  (var 1) @ (var 0)

@[simp] theorem betaEtaPaperSource_closedAtDepth :
    Term.closedAtDepth 2 betaEtaPaperSource = true := by
  native_decide

@[simp] theorem betaEtaPaperTarget_closedAtDepth :
    Term.closedAtDepth 2 betaEtaPaperTarget = true := by
  native_decide

@[simp] theorem betaEtaPaperFunction_closedAtDepth :
    Term.closedAtDepth 2 (ƛ ((var 2) @ (var 0))) = true := by
  native_decide

@[simp] theorem betaEtaPaperVarX_closedAtDepth :
    Term.closedAtDepth 2 (var 1) = true := by
  native_decide

/-- The direct β-contraction `(λz.xz) y →β xy`. -/
def betaEtaPaper_beta : BetaEtaStep betaEtaPaperSource betaEtaPaperTarget :=
  BetaEtaStep.beta (BetaStep.beta ((var 2) @ (var 0)) (var 0))

/-- The η-side contraction `(λz.xz) y →η xy`, obtained by η-contracting the
function part and whiskering that contraction through application. -/
def betaEtaPaper_eta : BetaEtaStep betaEtaPaperSource betaEtaPaperTarget := by
  apply BetaEtaStep.eta
  apply EtaStep.appL
  refine EtaStep.eta (var 2) ?_
  simp [Term.hasFreeVar]

/-- The paper's β-side witness packaged as an explicit 1-term. -/
def betaEtaPaper_beta1 : NTerm1 betaEtaPaperSource betaEtaPaperTarget :=
  NTerm1.redex betaEtaPaper_beta

/-- The paper's η-side witness packaged as an explicit 1-term. -/
def betaEtaPaper_eta1 : NTerm1 betaEtaPaperSource betaEtaPaperTarget :=
  NTerm1.redex betaEtaPaper_eta

/-- The function part `λz.xz` of the paper's witness term already collapses to
`x` under the continuous term interpreter. This is the object-level η-side
bridge that the proof-relevant semantics must later refine. -/
@[simp] theorem betaEtaPaperFunction_interpretContinuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (ρ : (SemanticContext K 2).Obj) :
    (interpretContinuous R.toReflexiveCHPO 2
        (ƛ ((var 2) @ (var 0))) betaEtaPaperFunction_closedAtDepth).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO 2
        (var 1) betaEtaPaperVarX_closedAtDepth).toFun ρ := by
  simpa [Term.shift1] using
    eta_sound_continuous R 2 (var 1) betaEtaPaperVarX_closedAtDepth ρ

/-- The paper's `(λz.xz) y` source already evaluates to the common target `xy`
under the continuous term interpreter. This is the object-level bridge that the
later β/η proof interpretation must refine to recover Example 4.2. -/
@[simp] theorem betaEtaPaperSource_interpretContinuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (ρ : (SemanticContext K 2).Obj) :
    (interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth).toFun ρ := by
  have hBody : Term.closedAtDepth 3 ((var 2) @ (var 0)) = true := by
    simpa [Term.closedAtDepth] using betaEtaPaperFunction_closedAtDepth
  have hArg : Term.closedAtDepth 2 (var 0) = true := by
    native_decide
  simpa [betaEtaPaperSource, betaEtaPaperTarget]
    using
      beta_sound_continuous
        R 2 ((var 2) @ (var 0)) (var 0) hBody hArg betaEtaPaperTarget_closedAtDepth ρ

/-- The explicit β-side 1-witness from the paper already collapses its endpoints
under the continuous interpreter. -/
@[simp] theorem betaEtaPaper_beta1_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (ρ : (SemanticContext K 2).Obj) :
    (interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth).toFun ρ := by
  exact
    betaEtaStep_sound_continuous
      R betaEtaPaper_beta
      betaEtaPaperSource_closedAtDepth
      betaEtaPaperTarget_closedAtDepth
      ρ

/-- The explicit η-side 1-witness from the paper also collapses its endpoints
under the continuous interpreter. This is the first theorem phrased directly in
terms of the paper's chosen η witness rather than only the intermediate function
contraction `λz.xz ↦ x`. -/
@[simp] theorem betaEtaPaper_eta1_sound_continuous
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K)
    (ρ : (SemanticContext K 2).Obj) :
    (interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth).toFun ρ =
      (interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth).toFun ρ := by
  exact
    betaEtaStep_sound_continuous
      R betaEtaPaper_eta
      betaEtaPaperSource_closedAtDepth
      betaEtaPaperTarget_closedAtDepth
      ρ

/-- The explicit β-side witness packaged as an equality of the two continuous
endpoint maps at depth `2`. This is the equality-generated continuous analogue
of `beta1Term_in_Theory1` specialized to the paper's open witness term. -/
noncomputable def betaEtaPaper_beta1_continuousWitness
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K) :
    interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth := by
  apply ContinuousMap.ext
  intro ρ
  exact betaEtaPaper_beta1_sound_continuous R ρ

/-- The explicit η-side witness packaged as an equality of the two continuous
endpoint maps at depth `2`. This is the first direct continuous interpretation
object for the paper's η witness itself, not just its endpoint equality. -/
noncomputable def betaEtaPaper_eta1_continuousWitness
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K) :
    interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth := by
  apply ContinuousMap.ext
  intro ρ
  exact betaEtaPaper_eta1_sound_continuous R ρ

/-- A proof-relevant wrapper for the two direct one-step witnesses appearing in
the paper's Example 4.2 source-to-target span. Unlike `NTerm1.redex`, this type
remembers whether the chosen witness was the β-side or η-side contraction. -/
inductive Example42DirectWitness where
  | beta
  | eta

/-- Forget the proof-relevant witness choice back to the repository's ordinary
1-term witness type. -/
def Example42DirectWitness.toNTerm1 : Example42DirectWitness →
    NTerm1 betaEtaPaperSource betaEtaPaperTarget
  | .beta => betaEtaPaper_beta1
  | .eta => betaEtaPaper_eta1

/-- At the `NTerm1` level, the direct β and η redex witnesses are already
identified because `BetaEtaStep` is proposition-valued. This is exactly why the
paper-facing bridge needs an additional proof-relevant wrapper. -/
theorem betaEtaPaper_beta1_eq_eta1 :
    betaEtaPaper_beta1 = betaEtaPaper_eta1 := by
  exact congrArg NTerm1.redex (Subsingleton.elim betaEtaPaper_beta betaEtaPaper_eta)

@[simp] theorem Example42DirectWitness.beta_toNTerm1 :
    Example42DirectWitness.toNTerm1 .beta = betaEtaPaper_beta1 := rfl

@[simp] theorem Example42DirectWitness.eta_toNTerm1 :
    Example42DirectWitness.toNTerm1 .eta = betaEtaPaper_eta1 := rfl

/-- The distinguished stage-0 sphere point canonically attached to one of the
paper's direct β/η witness shapes. -/
def Example42DirectWitness.stage0Point : Example42DirectWitness → SpherePoint
  | .beta => s1Right
  | .eta => s1Left

/-- The corresponding chosen `K∞` point, obtained by embedding the tagged
stage-0 sphere point into the inverse limit. -/
noncomputable def Example42DirectWitness.point
    (w : Example42DirectWitness) : KInfinityCHPO.Obj :=
  embedBaseToLimit (some w.stage0Point)

@[simp] theorem Example42DirectWitness.beta_stage0Point :
    Example42DirectWitness.stage0Point .beta = s1Right := rfl

@[simp] theorem Example42DirectWitness.eta_stage0Point :
    Example42DirectWitness.stage0Point .eta = s1Left := rfl

@[simp] theorem Example42DirectWitness.beta_point :
    Example42DirectWitness.point .beta = interp1Beta := rfl

@[simp] theorem Example42DirectWitness.eta_point :
    Example42DirectWitness.point .eta = interp1Eta := rfl

@[simp] theorem Example42DirectWitness.point_level0
    (w : Example42DirectWitness) :
    projectToLevel 0 w.point = some w.stage0Point := by
  cases w <;> rfl

/-- Chosen-data packaging of one of the paper's explicit Example 4.2
contraction witnesses together with the `K∞` point currently used to represent
it in the paper-facing non-equivalence interface. -/
structure Example42WitnessInterpretation where
  witness : NTerm1 betaEtaPaperSource betaEtaPaperTarget
  stage0Point : SpherePoint
  point : KInfinityCHPO.Obj
  point_level0 : projectToLevel 0 point = some stage0Point
  continuousWitness :
    interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth

/-- The β-side paper witness together with its chosen `K∞` representative. -/
noncomputable def betaEtaPaper_beta1_interpretation :
    Example42WitnessInterpretation where
  witness := Example42DirectWitness.toNTerm1 .beta
  stage0Point := Example42DirectWitness.stage0Point .beta
  point := Example42DirectWitness.point .beta
  point_level0 := Example42DirectWitness.point_level0 .beta
  continuousWitness := betaEtaPaper_beta1_continuousWitness kInfinityTwoSidedReflexiveCHPO

/-- The η-side paper witness together with its chosen `K∞` representative. -/
noncomputable def betaEtaPaper_eta1_interpretation :
    Example42WitnessInterpretation where
  witness := Example42DirectWitness.toNTerm1 .eta
  stage0Point := Example42DirectWitness.stage0Point .eta
  point := Example42DirectWitness.point .eta
  point_level0 := Example42DirectWitness.point_level0 .eta
  continuousWitness := betaEtaPaper_eta1_continuousWitness kInfinityTwoSidedReflexiveCHPO

/-- The chosen `K∞` representatives attached to the paper's explicit β₁ and η₁
witnesses are exactly the previously separated Example 4.2 points. -/
@[simp] theorem betaEtaPaper_beta1_interpretation_point :
    betaEtaPaper_beta1_interpretation.point = interp1Beta := rfl

@[simp] theorem betaEtaPaper_eta1_interpretation_point :
    betaEtaPaper_eta1_interpretation.point = interp1Eta := rfl

/-- Therefore the two packaged paper-witness interpretations are already
separated by the existing `K∞` Example 4.2 theorem. -/
theorem betaEtaPaper_witness_interpretations_distinct :
    betaEtaPaper_beta1_interpretation.point ≠
      betaEtaPaper_eta1_interpretation.point := by
  simpa using example_4_2

/-- And likewise there is no canonical `K∞` 1-cell between the chosen
representatives of the explicit β₁ and η₁ witnesses. -/
theorem betaEtaPaper_witness_interpretations_no_path :
    ¬ Nonempty
      (KInfinityPath
        betaEtaPaper_beta1_interpretation.point
        betaEtaPaper_eta1_interpretation.point) := by
  simpa using example_4_2_not_connected

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
2-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_2cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point} :
    ¬ Nonempty (KInfinityPath2 p q) := by
  intro h
  rcases h with ⟨α⟩
  simpa using example_4_2_no_path2 α

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
3-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_3cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point}
    {α β : KInfinityPath2 p q} :
    ¬ Nonempty (KInfinityPath3 α β) := by
  intro h
  rcases h with ⟨η⟩
  simpa using example_4_2_no_path3 η

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
4-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_4cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β} :
    ¬ Nonempty (KInfinityPath4 η θ) := by
  intro h
  rcases h with ⟨ω⟩
  simpa using example_4_2_no_path4 ω

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
5-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_5cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    {ω ξ : KInfinityPath4 η θ} :
    ¬ Nonempty (KInfinityPath5 ω ξ) := by
  intro h
  rcases h with ⟨μ⟩
  simpa using example_4_2_no_path5 μ

/-- The recursively completed all-dimensional separation also transfers to the
packaged β₁ / η₁ witness interpretations. -/
theorem betaEtaPaper_witness_interpretations_no_recursive_higher_cell
    (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = betaEtaPaper_beta1_interpretation.point ∧
          kInfinityTowerTargetObj x = betaEtaPaper_eta1_interpretation.point} := by
  simpa using example_4_2_no_recursive_higher_cell_nonempty n

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
