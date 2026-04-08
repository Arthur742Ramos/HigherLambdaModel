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

/-- The direct β-contraction `(λz.xz) y →β xy`, kept as a proof-relevant
one-step witness. -/
def betaEtaPaper_betaWitness :
    BetaEtaStepWitness betaEtaPaperSource betaEtaPaperTarget :=
  BetaEtaStepWitness.beta (BetaStepWitness.beta ((var 2) @ (var 0)) (var 0))

/-- The η-side contraction `(λz.xz) y →η xy`, kept as a proof-relevant
one-step witness. -/
def betaEtaPaper_etaWitness :
    BetaEtaStepWitness betaEtaPaperSource betaEtaPaperTarget := by
  apply BetaEtaStepWitness.eta
  apply EtaStepWitness.appL
  refine EtaStepWitness.eta (var 2) ?_
  simp [Term.hasFreeVar]

/-- The direct β-contraction `(λz.xz) y →β xy`. -/
def betaEtaPaper_beta : BetaEtaStep betaEtaPaperSource betaEtaPaperTarget :=
  betaEtaPaper_betaWitness.toBetaEtaStep

/-- The η-side contraction `(λz.xz) y →η xy`, obtained by η-contracting the
function part and whiskering that contraction through application. -/
def betaEtaPaper_eta : BetaEtaStep betaEtaPaperSource betaEtaPaperTarget :=
  betaEtaPaper_etaWitness.toBetaEtaStep

/-- The paper's β-side witness packaged in the new proof-relevant explicit
1-term language. -/
def betaEtaPaper_beta1Witness :
    NTerm1Witness betaEtaPaperSource betaEtaPaperTarget :=
  .redex betaEtaPaper_betaWitness

/-- The paper's η-side witness packaged in the new proof-relevant explicit
1-term language. -/
def betaEtaPaper_eta1Witness :
    NTerm1Witness betaEtaPaperSource betaEtaPaperTarget :=
  .redex betaEtaPaper_etaWitness

/-- The paper's β-side witness packaged as an explicit 1-term. -/
def betaEtaPaper_beta1 : NTerm1 betaEtaPaperSource betaEtaPaperTarget :=
  betaEtaPaper_beta1Witness.toNTerm1

/-- The paper's η-side witness packaged as an explicit 1-term. -/
def betaEtaPaper_eta1 : NTerm1 betaEtaPaperSource betaEtaPaperTarget :=
  betaEtaPaper_eta1Witness.toNTerm1

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
    betaEtaStepWitness_sound_continuous
      R betaEtaPaper_betaWitness
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
    betaEtaStepWitness_sound_continuous
      R betaEtaPaper_etaWitness
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
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth :=
  nterm1Witness_continuousWitness
    R betaEtaPaper_beta1Witness
    betaEtaPaperSource_closedAtDepth
    betaEtaPaperTarget_closedAtDepth

/-- The explicit η-side witness packaged as an equality of the two continuous
endpoint maps at depth `2`. This is the first direct continuous interpretation
object for the paper's η witness itself, not just its endpoint equality. -/
noncomputable def betaEtaPaper_eta1_continuousWitness
    {K : CompleteHomotopyPartialOrder}
    (R : TwoSidedReflexiveCHPO K) :
    interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous R.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth :=
  nterm1Witness_continuousWitness
    R betaEtaPaper_eta1Witness
    betaEtaPaperSource_closedAtDepth
    betaEtaPaperTarget_closedAtDepth

/-- A proof-relevant wrapper for the two direct one-step witnesses appearing in
the paper's Example 4.2 source-to-target span. Unlike `NTerm1.redex`, this type
remembers whether the chosen witness was the β-side or η-side contraction. -/
inductive Example42DirectWitness where
  | beta
  | eta
deriving DecidableEq

/-- Forget the paper's direct witness tag into the general proof-relevant
one-step βη witness layer. -/
def Example42DirectWitness.toStepWitness : Example42DirectWitness →
    BetaEtaStepWitness betaEtaPaperSource betaEtaPaperTarget
  | .beta => betaEtaPaper_betaWitness
  | .eta => betaEtaPaper_etaWitness

/-- Forget the proof-relevant witness choice back to the repository's ordinary
proof-relevant explicit 1-term language. -/
def Example42DirectWitness.toNTerm1Witness : Example42DirectWitness →
    NTerm1Witness betaEtaPaperSource betaEtaPaperTarget
  | .beta => betaEtaPaper_beta1Witness
  | .eta => betaEtaPaper_eta1Witness

@[simp] theorem Example42DirectWitness.beta_toNTerm1Witness :
    Example42DirectWitness.toNTerm1Witness .beta = betaEtaPaper_beta1Witness := rfl

@[simp] theorem Example42DirectWitness.eta_toNTerm1Witness :
    Example42DirectWitness.toNTerm1Witness .eta = betaEtaPaper_eta1Witness := rfl

/-- Forget the proof-relevant witness choice all the way back to the
repository's ordinary 1-term witness type. -/
def Example42DirectWitness.toNTerm1 : Example42DirectWitness →
    NTerm1 betaEtaPaperSource betaEtaPaperTarget
  | w => w.toNTerm1Witness.toNTerm1

/-- The new general proof-relevant one-step witness layer still distinguishes
the paper's β-side and η-side contractions. -/
theorem betaEtaPaper_betaWitness_ne_etaWitness :
    betaEtaPaper_betaWitness ≠ betaEtaPaper_etaWitness := by
  intro h
  cases h

/-- Unlike `toNTerm1`, forgetting only to the new proof-relevant step language
does retain the β/η distinction. -/
theorem Example42DirectWitness.toStepWitness_injective :
    Function.Injective Example42DirectWitness.toStepWitness := by
  intro w v h
  cases w <;> cases v
  · rfl
  · exact False.elim (betaEtaPaper_betaWitness_ne_etaWitness h)
  · exact False.elim (betaEtaPaper_betaWitness_ne_etaWitness h.symm)
  · rfl

/-- The proof-relevant explicit 1-term layer also retains the β/η distinction. -/
theorem Example42DirectWitness.toNTerm1Witness_injective :
    Function.Injective Example42DirectWitness.toNTerm1Witness := by
  intro w v h
  cases w <;> cases v
  · rfl
  · cases h
  · cases h
  · rfl

/-- At the `NTerm1` level, the direct β and η redex witnesses are already
identified because `BetaEtaStep` is proposition-valued. This is exactly why the
paper-facing bridge needs an additional proof-relevant wrapper. -/
theorem betaEtaPaper_beta1_eq_eta1 :
    betaEtaPaper_beta1 = betaEtaPaper_eta1 := by
  exact congrArg NTerm1.redex (Subsingleton.elim betaEtaPaper_beta betaEtaPaper_eta)

/-- Forgetting the direct witness tag to `NTerm1` erases the β/η distinction
completely. -/
theorem Example42DirectWitness.toNTerm1_eq
    (w v : Example42DirectWitness) :
    w.toNTerm1 = v.toNTerm1 := by
  cases w <;> cases v
  · rfl
  · exact betaEtaPaper_beta1_eq_eta1
  · exact betaEtaPaper_beta1_eq_eta1.symm
  · rfl

/-- Therefore the direct witness tag cannot be recovered from bare `NTerm1`
data. -/
theorem Example42DirectWitness.toNTerm1_not_injective :
    ¬ Function.Injective Example42DirectWitness.toNTerm1 := by
  intro hInj
  have hEq :
      Example42DirectWitness.toNTerm1 .beta =
        Example42DirectWitness.toNTerm1 .eta :=
    Example42DirectWitness.toNTerm1_eq .beta .eta
  have hWitness : (Example42DirectWitness.beta : Example42DirectWitness) = .eta :=
    hInj hEq
  cases hWitness

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

/-- Recover one of the paper's two direct witness tags from the stage-0 sphere
point used in the current `K∞` interpretation. -/
def Example42DirectWitness.ofStage0Point : SpherePoint → Option Example42DirectWitness
  | ⟨1, true⟩ => some .beta
  | ⟨1, false⟩ => some .eta
  | _ => none

@[simp] theorem Example42DirectWitness.ofStage0Point_s1Right :
    Example42DirectWitness.ofStage0Point s1Right = some .beta := rfl

@[simp] theorem Example42DirectWitness.ofStage0Point_s1Left :
    Example42DirectWitness.ofStage0Point s1Left = some .eta := rfl

@[simp] theorem Example42DirectWitness.ofStage0Point_stage0Point
    (w : Example42DirectWitness) :
    Example42DirectWitness.ofStage0Point w.stage0Point = some w := by
  cases w <;> rfl

/-- Recover a direct witness tag from the level-0 projection of a `K∞` point,
when that point comes from the current Example 4.2 direct witness layer. -/
def Example42DirectWitness.recoverFromPoint
    (x : KInfinityCHPO.Obj) : Option Example42DirectWitness :=
  Option.bind (projectToLevel 0 x) Example42DirectWitness.ofStage0Point

@[simp] theorem Example42DirectWitness.recoverFromPoint_point
    (w : Example42DirectWitness) :
    Example42DirectWitness.recoverFromPoint w.point = some w := by
  simp [Example42DirectWitness.recoverFromPoint, Example42DirectWitness.point_level0]

/-- Canonical continuous equality attached to one of the paper's two direct
witness tags. This is the proof-relevant continuous witness map for the current
Example 4.2 bridge. -/
noncomputable def Example42DirectWitness.continuousWitness
    (w : Example42DirectWitness) :
    interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth :=
  nterm1Witness_continuousWitness
    kInfinityTwoSidedReflexiveCHPO
    w.toNTerm1Witness
    betaEtaPaperSource_closedAtDepth
    betaEtaPaperTarget_closedAtDepth

@[simp] theorem Example42DirectWitness.beta_continuousWitness :
    Example42DirectWitness.continuousWitness .beta =
      betaEtaPaper_beta1_continuousWitness kInfinityTwoSidedReflexiveCHPO := rfl

@[simp] theorem Example42DirectWitness.eta_continuousWitness :
    Example42DirectWitness.continuousWitness .eta =
      betaEtaPaper_eta1_continuousWitness kInfinityTwoSidedReflexiveCHPO := rfl

/-- The proof-relevant direct witness map to `K∞` points is injective: once the
continuous equality is paired with its chosen `K∞` point, the β/η distinction is
visible again. -/
theorem Example42DirectWitness.point_injective :
    Function.Injective Example42DirectWitness.point := by
  intro w v hPoint
  cases w <;> cases v
  · rfl
  · exact False.elim (example_4_2 hPoint)
  · exact False.elim (example_4_2 hPoint.symm)
  · rfl

/-- Distinct proof-relevant witness tags select distinct `K∞` points. -/
theorem Example42DirectWitness.point_ne_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v) :
    w.point ≠ v.point := by
  intro hPoint
  exact h (Example42DirectWitness.point_injective hPoint)

/-- Distinct proof-relevant witness tags admit no 1-cell between their chosen
`K∞` points. -/
theorem Example42DirectWitness.no_path_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v) :
    ¬ Nonempty (KInfinityPath w.point v.point) := by
  intro hp
  rcases hp with ⟨p⟩
  exact h (Example42DirectWitness.point_injective p.down)

/-- Distinct proof-relevant witness tags inherit the existing 2-cell
separation. -/
theorem Example42DirectWitness.no_2cell_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v)
    {p q : KInfinityPath w.point v.point} :
    ¬ Nonempty (KInfinityPath2 p q) := by
  intro h2
  exact Example42DirectWitness.no_path_of_ne h ⟨p⟩

/-- Distinct proof-relevant witness tags inherit the existing 3-cell
separation. -/
theorem Example42DirectWitness.no_3cell_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v)
    {p q : KInfinityPath w.point v.point}
    {α β : KInfinityPath2 p q} :
    ¬ Nonempty (KInfinityPath3 α β) := by
  intro h3
  exact Example42DirectWitness.no_2cell_of_ne h ⟨α⟩

/-- Distinct proof-relevant witness tags inherit the existing 4-cell
separation. -/
theorem Example42DirectWitness.no_4cell_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v)
    {p q : KInfinityPath w.point v.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β} :
    ¬ Nonempty (KInfinityPath4 η θ) := by
  intro h4
  exact Example42DirectWitness.no_3cell_of_ne h ⟨η⟩

/-- Distinct proof-relevant witness tags inherit the existing 5-cell
separation. -/
theorem Example42DirectWitness.no_5cell_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v)
    {p q : KInfinityPath w.point v.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    {ω ξ : KInfinityPath4 η θ} :
    ¬ Nonempty (KInfinityPath5 ω ξ) := by
  intro h5
  exact Example42DirectWitness.no_4cell_of_ne h ⟨ω⟩

/-- Distinct proof-relevant witness tags also inherit the recursively completed
all-dimensional separation. -/
theorem Example42DirectWitness.no_recursive_higher_cell_of_ne
    {w v : Example42DirectWitness} (h : w ≠ v)
    (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = w.point ∧
          kInfinityTowerTargetObj x = v.point} := by
  intro hx
  rcases hx with ⟨⟨x, hs, ht⟩⟩
  have hPoint : w.point = v.point := by
    calc
      w.point = kInfinityTowerSourceObj x := hs.symm
      _ = kInfinityTowerTargetObj x := kInfinityTower_source_eq_target x
      _ = v.point := ht
  exact h (Example42DirectWitness.point_injective hPoint)

/-- Canonical proof-relevant packaging of one of the paper's two direct
witnesses. The chosen stage-0 and `K∞` points are read directly from the witness
tag, rather than inserted manually after forgetting to `NTerm1`. -/
structure Example42DirectWitnessInterpretation where
  witness : Example42DirectWitness
  point_level0 : projectToLevel 0 witness.point = some witness.stage0Point
  continuousWitness :
    interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth

/-- The distinguished stage-0 point carried by a proof-relevant witness
interpretation. -/
def Example42DirectWitnessInterpretation.stage0Point
    (I : Example42DirectWitnessInterpretation) : SpherePoint :=
  I.witness.stage0Point

/-- The corresponding chosen `K∞` point carried by a proof-relevant witness
interpretation. -/
noncomputable def Example42DirectWitnessInterpretation.point
    (I : Example42DirectWitnessInterpretation) : KInfinityCHPO.Obj :=
  I.witness.point

@[simp] theorem Example42DirectWitnessInterpretation.point_level0'
    (I : Example42DirectWitnessInterpretation) :
    projectToLevel 0 I.point = some I.stage0Point :=
  I.point_level0

/-- Canonical proof-relevant interpretation of one of the paper's two direct
witness tags. -/
noncomputable def Example42DirectWitness.interpretation
    (w : Example42DirectWitness) : Example42DirectWitnessInterpretation where
  witness := w
  point_level0 := w.point_level0
  continuousWitness := w.continuousWitness

@[simp] theorem Example42DirectWitness.interpretation_stage0Point
    (w : Example42DirectWitness) :
    (w.interpretation).stage0Point = w.stage0Point := rfl

@[simp] theorem Example42DirectWitness.interpretation_point
    (w : Example42DirectWitness) :
    (w.interpretation).point = w.point := rfl

/-- Chosen-data packaging of one of the paper's explicit Example 4.2
contraction witnesses together with the `K∞` point currently used to represent
it in the paper-facing non-equivalence interface. -/
structure Example42NTerm1WitnessInterpretation where
  witness : NTerm1Witness betaEtaPaperSource betaEtaPaperTarget
  stage0Point : SpherePoint
  point : KInfinityCHPO.Obj
  point_level0 : projectToLevel 0 point = some stage0Point
  continuousWitness :
    interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperSource betaEtaPaperSource_closedAtDepth =
      interpretContinuous kInfinityTwoSidedReflexiveCHPO.toReflexiveCHPO 2
        betaEtaPaperTarget betaEtaPaperTarget_closedAtDepth

/-- Forget a proof-relevant direct witness interpretation to the generic
proof-relevant explicit 1-term language. -/
noncomputable def Example42DirectWitnessInterpretation.toNTerm1WitnessInterpretation
    (I : Example42DirectWitnessInterpretation) : Example42NTerm1WitnessInterpretation where
  witness := I.witness.toNTerm1Witness
  stage0Point := I.stage0Point
  point := I.point
  point_level0 := I.point_level0
  continuousWitness := I.continuousWitness

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

/-- Forget a proof-relevant direct witness interpretation back to the older
paper-facing chosen-data package. -/
noncomputable def Example42NTerm1WitnessInterpretation.toWitnessInterpretation
    (I : Example42NTerm1WitnessInterpretation) : Example42WitnessInterpretation where
  witness := I.witness.toNTerm1
  stage0Point := I.stage0Point
  point := I.point
  point_level0 := I.point_level0
  continuousWitness := I.continuousWitness

/-- Forget a proof-relevant direct witness interpretation back to the older
paper-facing chosen-data package. -/
noncomputable def Example42DirectWitnessInterpretation.toWitnessInterpretation
    (I : Example42DirectWitnessInterpretation) : Example42WitnessInterpretation :=
  I.toNTerm1WitnessInterpretation.toWitnessInterpretation

@[simp] theorem Example42NTerm1WitnessInterpretation.toWitnessInterpretation_point
    (I : Example42NTerm1WitnessInterpretation) :
    I.toWitnessInterpretation.point = I.point := rfl

@[simp] theorem Example42DirectWitnessInterpretation.toNTerm1WitnessInterpretation_point
    (I : Example42DirectWitnessInterpretation) :
    I.toNTerm1WitnessInterpretation.point = I.point := rfl

@[simp] theorem Example42DirectWitnessInterpretation.toNTerm1WitnessInterpretation_witness
    (I : Example42DirectWitnessInterpretation) :
    I.toNTerm1WitnessInterpretation.witness = I.witness.toNTerm1Witness := rfl

@[simp] theorem Example42DirectWitnessInterpretation.toWitnessInterpretation_witness
    (I : Example42DirectWitnessInterpretation) :
    I.toWitnessInterpretation.witness = I.witness.toNTerm1 := rfl

@[simp] theorem Example42DirectWitnessInterpretation.toWitnessInterpretation_point
    (I : Example42DirectWitnessInterpretation) :
    I.toWitnessInterpretation.point = I.point := rfl

private theorem no_betaStepWitness_from_var
    {n : Nat} {N : Term} :
    BetaStepWitness (var n) N → False := by
  intro h
  cases h

private theorem no_etaStepWitness_from_var
    {n : Nat} {N : Term} :
    EtaStepWitness (var n) N → False := by
  intro h
  cases h

private theorem no_betaStepWitness_from_example42Body
    {N : Term} :
    BetaStepWitness ((var 2) @ (var 0)) N → False := by
  intro h
  cases h with
  | appL hL => exact no_betaStepWitness_from_var hL
  | appR hR => exact no_betaStepWitness_from_var hR

private theorem no_etaStepWitness_from_example42Body
    {N : Term} :
    EtaStepWitness ((var 2) @ (var 0)) N → False := by
  intro h
  cases h with
  | appL hL => exact no_etaStepWitness_from_var hL
  | appR hR => exact no_etaStepWitness_from_var hR

private theorem no_betaEtaStepWitness_from_target
    {N : Term} :
    BetaEtaStepWitness betaEtaPaperTarget N → False := by
  intro h
  cases h with
  | beta hb =>
      cases hb with
      | appL hL => exact no_betaStepWitness_from_var hL
      | appR hR => exact no_betaStepWitness_from_var hR
  | eta he =>
      cases he with
      | appL hL => exact no_etaStepWitness_from_var hL
      | appR hR => exact no_etaStepWitness_from_var hR

/-- Reflexive padding inside the paper's explicit proof-relevant 1-term
language. -/
private inductive Example42Trivial :
    {M N : Term} → NTerm1Witness M N → Prop where
  | refl {M : Term} :
      Example42Trivial (NTerm1Witness.refl (M := M))
  | seq {M P N : Term}
      {t₁ : NTerm1Witness M P} {t₂ : NTerm1Witness P N} :
      Example42Trivial t₁ →
      Example42Trivial t₂ →
      Example42Trivial (NTerm1Witness.seq t₁ t₂)

private theorem example42Trivial_eq
    {M N : Term} {t : NTerm1Witness M N}
    (h : Example42Trivial t) :
    N = M := by
  induction h with
  | refl =>
      rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      exact ih₂.trans ih₁

/-- β-reachability on the paper's explicit witness span: after removing
reflexive padding, the witness is the direct β contraction. -/
private inductive Example42BetaReachable :
    {M N : Term} → NTerm1Witness M N → Prop where
  | beta :
      Example42BetaReachable betaEtaPaper_beta1Witness
  | seqLeft {M P N : Term}
      {t₁ : NTerm1Witness M P} {t₂ : NTerm1Witness P N} :
      Example42Trivial t₁ →
      Example42BetaReachable t₂ →
      Example42BetaReachable (NTerm1Witness.seq t₁ t₂)
  | seqRight {M P N : Term}
      {t₁ : NTerm1Witness M P} {t₂ : NTerm1Witness P N} :
      Example42BetaReachable t₁ →
      Example42Trivial t₂ →
      Example42BetaReachable (NTerm1Witness.seq t₁ t₂)

/-- η-reachability on the paper's explicit witness span: after removing
reflexive padding, the witness is the direct η contraction. -/
private inductive Example42EtaReachable :
    {M N : Term} → NTerm1Witness M N → Prop where
  | eta :
      Example42EtaReachable betaEtaPaper_eta1Witness
  | seqLeft {M P N : Term}
      {t₁ : NTerm1Witness M P} {t₂ : NTerm1Witness P N} :
      Example42Trivial t₁ →
      Example42EtaReachable t₂ →
      Example42EtaReachable (NTerm1Witness.seq t₁ t₂)
  | seqRight {M P N : Term}
      {t₁ : NTerm1Witness M P} {t₂ : NTerm1Witness P N} :
      Example42EtaReachable t₁ →
      Example42Trivial t₂ →
      Example42EtaReachable (NTerm1Witness.seq t₁ t₂)

private theorem example42BetaReachable_endpoints
    {M N : Term} {t : NTerm1Witness M N}
    (h : Example42BetaReachable t) :
    M = betaEtaPaperSource ∧ N = betaEtaPaperTarget := by
  induction h with
  | beta =>
      constructor <;> rfl
  | seqLeft h₁ h₂ ih =>
      rcases ih with ⟨hP, hN⟩
      have hPM := example42Trivial_eq h₁
      constructor
      · exact hPM.symm.trans hP
      · exact hN
  | seqRight h₁ h₂ ih =>
      rcases ih with ⟨hM, hP⟩
      have hNP := example42Trivial_eq h₂
      constructor
      · exact hM
      · exact hNP.trans hP

private theorem example42EtaReachable_endpoints
    {M N : Term} {t : NTerm1Witness M N}
    (h : Example42EtaReachable t) :
    M = betaEtaPaperSource ∧ N = betaEtaPaperTarget := by
  induction h with
  | eta =>
      constructor <;> rfl
  | seqLeft h₁ h₂ ih =>
      rcases ih with ⟨hP, hN⟩
      have hPM := example42Trivial_eq h₁
      constructor
      · exact hPM.symm.trans hP
      · exact hN
  | seqRight h₁ h₂ ih =>
      rcases ih with ⟨hM, hP⟩
      have hNP := example42Trivial_eq h₂
      constructor
      · exact hM
      · exact hNP.trans hP

private theorem betaEtaPaperSource_ne_target :
    betaEtaPaperSource ≠ betaEtaPaperTarget := by
  decide

/-- Any explicit proof-relevant 1-term starting at the paper source or target is
either reflexive padding, β-reachable, or η-reachable. -/
private theorem example42NTerm1Witness_classify
    {M N : Term} (t : NTerm1Witness M N) :
    M = betaEtaPaperSource ∨ M = betaEtaPaperTarget →
      Example42Trivial t ∨ Example42BetaReachable t ∨ Example42EtaReachable t := by
  induction t with
  | refl =>
      intro hM
      exact Or.inl Example42Trivial.refl
  | redex s =>
      intro hM
      rcases hM with rfl | rfl
      · cases s with
        | beta hb =>
            cases hb with
            | beta M N =>
                exact Or.inr <| Or.inl <|
                  by simpa [betaEtaPaper_beta1Witness, betaEtaPaper_betaWitness]
                    using (Example42BetaReachable.beta :
                      Example42BetaReachable betaEtaPaper_beta1Witness)
            | appL hL =>
                cases hL with
                | lam hBody =>
                    exact False.elim (no_betaStepWitness_from_example42Body hBody)
            | appR hR =>
                exact False.elim (no_betaStepWitness_from_var hR)
        | eta he =>
            cases he with
            | appL hL =>
                cases hL with
                | eta M hFree =>
                    exact Or.inr <| Or.inr <|
                      by simpa [betaEtaPaper_eta1Witness, betaEtaPaper_etaWitness]
                        using (Example42EtaReachable.eta :
                          Example42EtaReachable betaEtaPaper_eta1Witness)
                | lam hBody =>
                    exact False.elim (no_etaStepWitness_from_example42Body hBody)
            | appR hR =>
                exact False.elim (no_etaStepWitness_from_var hR)
      · exact False.elim (no_betaEtaStepWitness_from_target s)
  | seq t₁ t₂ ih₁ ih₂ =>
      intro hM
      have h₁ := ih₁ hM
      rcases h₁ with h₁triv | h₁rest
      · have hPM := example42Trivial_eq h₁triv
        cases hPM
        have h₂ := ih₂ hM
        rcases h₂ with h₂triv | h₂rest
        · exact Or.inl (Example42Trivial.seq h₁triv h₂triv)
        · rcases h₂rest with h₂beta | h₂eta
          · exact Or.inr <| Or.inl
              (Example42BetaReachable.seqLeft h₁triv h₂beta)
          · exact Or.inr <| Or.inr
              (Example42EtaReachable.seqLeft h₁triv h₂eta)
      · rcases h₁rest with h₁beta | h₁eta
        · have hP := (example42BetaReachable_endpoints h₁beta).2
          cases hP
          have h₂ := ih₂ (Or.inr rfl)
          rcases h₂ with h₂triv | h₂rest
          · exact Or.inr <| Or.inl
              (Example42BetaReachable.seqRight h₁beta h₂triv)
          · rcases h₂rest with h₂beta | h₂eta
            · have hStart : betaEtaPaperTarget = betaEtaPaperSource :=
                (example42BetaReachable_endpoints h₂beta).1
              exact False.elim (betaEtaPaperSource_ne_target hStart.symm)
            · have hStart : betaEtaPaperTarget = betaEtaPaperSource :=
                (example42EtaReachable_endpoints h₂eta).1
              exact False.elim (betaEtaPaperSource_ne_target hStart.symm)
        · have hP := (example42EtaReachable_endpoints h₁eta).2
          cases hP
          have h₂ := ih₂ (Or.inr rfl)
          rcases h₂ with h₂triv | h₂rest
          · exact Or.inr <| Or.inr
              (Example42EtaReachable.seqRight h₁eta h₂triv)
          · rcases h₂rest with h₂beta | h₂eta
            · have hStart : betaEtaPaperTarget = betaEtaPaperSource :=
                (example42BetaReachable_endpoints h₂beta).1
              exact False.elim (betaEtaPaperSource_ne_target hStart.symm)
            · have hStart : betaEtaPaperTarget = betaEtaPaperSource :=
                (example42EtaReachable_endpoints h₂eta).1
              exact False.elim (betaEtaPaperSource_ne_target hStart.symm)

private theorem example42NTerm1Witness_beta_or_eta
    (t : NTerm1Witness betaEtaPaperSource betaEtaPaperTarget) :
    Example42BetaReachable t ∨ Example42EtaReachable t := by
  have h := example42NTerm1Witness_classify t (Or.inl rfl)
  rcases h with hTriv | hRest
  · have hEq : betaEtaPaperTarget = betaEtaPaperSource :=
        example42Trivial_eq (t := t) hTriv
    exact False.elim (betaEtaPaperSource_ne_target hEq.symm)
  · exact hRest

private theorem example42Eta1Witness_not_beta :
    ¬ Example42BetaReachable betaEtaPaper_eta1Witness := by
  intro h
  cases h

private theorem example42Beta1Witness_not_eta :
    ¬ Example42EtaReachable betaEtaPaper_beta1Witness := by
  intro h
  cases h

/-- The proof-relevant explicit Example 4.2 witness tag attached to an arbitrary
`NTerm1Witness betaEtaPaperSource betaEtaPaperTarget`, obtained from the
Prop-level β/η reachability classification. -/
noncomputable def example42NTerm1WitnessTag
    (t : NTerm1Witness betaEtaPaperSource betaEtaPaperTarget) :
    Example42DirectWitness := by
  classical
  exact if h : Example42BetaReachable t then .beta else .eta

/-- The chosen stage-0 point associated to a proof-relevant explicit Example 4.2
witness is determined by its Prop-level β/η classification. -/
noncomputable def example42NTerm1Witness_stage0Point
    (t : NTerm1Witness betaEtaPaperSource betaEtaPaperTarget) : SpherePoint :=
  (example42NTerm1WitnessTag t).stage0Point

/-- The chosen `K∞` point associated to a proof-relevant explicit Example 4.2
witness is determined by its Prop-level β/η classification. -/
noncomputable def example42NTerm1Witness_point
    (t : NTerm1Witness betaEtaPaperSource betaEtaPaperTarget) : KInfinityCHPO.Obj :=
  (example42NTerm1WitnessTag t).point

/-- Generic chosen-data interpretation for proof-relevant explicit Example 4.2
witnesses, now defined from the Prop-level β/η reachability classification
instead of the bespoke two-tag selector. -/
noncomputable def example42NTerm1Witness_interpretation
    (t : NTerm1Witness betaEtaPaperSource betaEtaPaperTarget) :
    Example42NTerm1WitnessInterpretation where
  witness := t
  stage0Point := example42NTerm1Witness_stage0Point t
  point := example42NTerm1Witness_point t
  point_level0 := (example42NTerm1WitnessTag t).point_level0
  continuousWitness :=
    nterm1Witness_continuousWitness kInfinityTwoSidedReflexiveCHPO
      t betaEtaPaperSource_closedAtDepth betaEtaPaperTarget_closedAtDepth

/-- The β-side paper witness in the generic proof-relevant explicit 1-term
language together with its chosen `K∞` representative. -/
noncomputable def betaEtaPaper_beta1Witness_interpretation :
    Example42NTerm1WitnessInterpretation :=
  example42NTerm1Witness_interpretation betaEtaPaper_beta1Witness

/-- The η-side paper witness in the generic proof-relevant explicit 1-term
language together with its chosen `K∞` representative. -/
noncomputable def betaEtaPaper_eta1Witness_interpretation :
    Example42NTerm1WitnessInterpretation :=
  example42NTerm1Witness_interpretation betaEtaPaper_eta1Witness

@[simp] theorem example42NTerm1WitnessTag_beta :
    example42NTerm1WitnessTag betaEtaPaper_beta1Witness = .beta := by
  classical
  unfold example42NTerm1WitnessTag
  simp [Example42BetaReachable.beta]

@[simp] theorem example42NTerm1WitnessTag_eta :
    example42NTerm1WitnessTag betaEtaPaper_eta1Witness = .eta := by
  classical
  unfold example42NTerm1WitnessTag
  simp [example42Eta1Witness_not_beta]

/-- The distinguished points of the proof-relevant explicit 1-term
interpretations are the same Example 4.2 points as before. -/
@[simp] theorem betaEtaPaper_beta1Witness_interpretation_point :
    betaEtaPaper_beta1Witness_interpretation.point = interp1Beta := by
  simp [betaEtaPaper_beta1Witness_interpretation, example42NTerm1Witness_interpretation,
    example42NTerm1Witness_point]

@[simp] theorem betaEtaPaper_eta1Witness_interpretation_point :
    betaEtaPaper_eta1Witness_interpretation.point = interp1Eta := by
  simp [betaEtaPaper_eta1Witness_interpretation, example42NTerm1Witness_interpretation,
    example42NTerm1Witness_point]

/-- The proof-relevant explicit 1-term witness interpretations are already
separated by the existing `K∞` Example 4.2 theorem. -/
theorem betaEtaPaper_nterm1Witness_interpretations_distinct :
    betaEtaPaper_beta1Witness_interpretation.point ≠
      betaEtaPaper_eta1Witness_interpretation.point := by
  simpa using
    Example42DirectWitness.point_ne_of_ne
      (w := .beta) (v := .eta) (by decide)

/-- And likewise there is no canonical `K∞` 1-cell between the chosen
representatives of the proof-relevant β₁ and η₁ witnesses. -/
theorem betaEtaPaper_nterm1Witness_interpretations_no_path :
    ¬ Nonempty
      (KInfinityPath
        betaEtaPaper_beta1Witness_interpretation.point
        betaEtaPaper_eta1Witness_interpretation.point) := by
  simpa using
    Example42DirectWitness.no_path_of_ne
      (w := .beta) (v := .eta) (by decide)

/-- The proof-relevant explicit β₁ / η₁ witness interpretations also inherit the
existing 2-cell separation. -/
theorem betaEtaPaper_nterm1Witness_interpretations_no_2cell
    {p q : KInfinityPath
      betaEtaPaper_beta1Witness_interpretation.point
      betaEtaPaper_eta1Witness_interpretation.point} :
    ¬ Nonempty (KInfinityPath2 p q) := by
  intro h2
  exact betaEtaPaper_nterm1Witness_interpretations_no_path ⟨p⟩

/-- The proof-relevant explicit β₁ / η₁ witness interpretations also inherit the
existing 3-cell separation. -/
theorem betaEtaPaper_nterm1Witness_interpretations_no_3cell
    {p q : KInfinityPath
      betaEtaPaper_beta1Witness_interpretation.point
      betaEtaPaper_eta1Witness_interpretation.point}
    {α β : KInfinityPath2 p q} :
    ¬ Nonempty (KInfinityPath3 α β) := by
  intro h3
  exact betaEtaPaper_nterm1Witness_interpretations_no_2cell ⟨α⟩

/-- The proof-relevant explicit β₁ / η₁ witness interpretations also inherit the
existing 4-cell separation. -/
theorem betaEtaPaper_nterm1Witness_interpretations_no_4cell
    {p q : KInfinityPath
      betaEtaPaper_beta1Witness_interpretation.point
      betaEtaPaper_eta1Witness_interpretation.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β} :
    ¬ Nonempty (KInfinityPath4 η θ) := by
  intro h4
  exact betaEtaPaper_nterm1Witness_interpretations_no_3cell ⟨η⟩

/-- The proof-relevant explicit β₁ / η₁ witness interpretations also inherit the
existing 5-cell separation. -/
theorem betaEtaPaper_nterm1Witness_interpretations_no_5cell
    {p q : KInfinityPath
      betaEtaPaper_beta1Witness_interpretation.point
      betaEtaPaper_eta1Witness_interpretation.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    {μ ν : KInfinityPath4 η θ} :
    ¬ Nonempty (KInfinityPath5 μ ν) := by
  intro h5
  exact betaEtaPaper_nterm1Witness_interpretations_no_4cell ⟨μ⟩

/-- The proof-relevant explicit β₁ / η₁ witness interpretations also inherit the
all-dimensional recursive higher-cell separation. -/
theorem betaEtaPaper_nterm1Witness_interpretations_no_recursive_higher_cell
    (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = betaEtaPaper_beta1Witness_interpretation.point ∧
          kInfinityTowerTargetObj x = betaEtaPaper_eta1Witness_interpretation.point} := by
  simpa using
    (Example42DirectWitness.no_recursive_higher_cell_of_ne
      (w := .beta) (v := .eta) (by decide) n)

/-- The β-side paper witness together with its chosen `K∞` representative. -/
noncomputable def betaEtaPaper_beta1_interpretation :
    Example42WitnessInterpretation :=
  betaEtaPaper_beta1Witness_interpretation.toWitnessInterpretation

/-- The η-side paper witness together with its chosen `K∞` representative. -/
noncomputable def betaEtaPaper_eta1_interpretation :
    Example42WitnessInterpretation :=
  betaEtaPaper_eta1Witness_interpretation.toWitnessInterpretation

/-- The chosen `K∞` representatives attached to the paper's explicit β₁ and η₁
witnesses are exactly the previously separated Example 4.2 points. -/
@[simp] theorem betaEtaPaper_beta1_interpretation_point :
    betaEtaPaper_beta1_interpretation.point = interp1Beta := by
  simpa [betaEtaPaper_beta1_interpretation] using
    betaEtaPaper_beta1Witness_interpretation_point

@[simp] theorem betaEtaPaper_eta1_interpretation_point :
    betaEtaPaper_eta1_interpretation.point = interp1Eta := by
  simpa [betaEtaPaper_eta1_interpretation] using
    betaEtaPaper_eta1Witness_interpretation_point

/-- Therefore the two packaged paper-witness interpretations are already
separated by the existing `K∞` Example 4.2 theorem. -/
theorem betaEtaPaper_witness_interpretations_distinct :
    betaEtaPaper_beta1_interpretation.point ≠
      betaEtaPaper_eta1_interpretation.point := by
  intro hPoint
  have hPoint' : interp1Beta = interp1Eta := by
    calc
      interp1Beta = betaEtaPaper_beta1_interpretation.point := by
        symm
        exact betaEtaPaper_beta1_interpretation_point
      _ = betaEtaPaper_eta1_interpretation.point := hPoint
      _ = interp1Eta := betaEtaPaper_eta1_interpretation_point
  exact Example42DirectWitness.point_ne_of_ne
    (w := .beta) (v := .eta) (by decide) hPoint'

/-- And likewise there is no canonical `K∞` 1-cell between the chosen
representatives of the explicit β₁ and η₁ witnesses. -/
theorem betaEtaPaper_witness_interpretations_no_path :
    ¬ Nonempty
      (KInfinityPath
        betaEtaPaper_beta1_interpretation.point
        betaEtaPaper_eta1_interpretation.point) := by
  intro hp
  rcases hp with ⟨p⟩
  have p' : KInfinityPath interp1Beta interp1Eta := by
    simpa using p
  exact Example42DirectWitness.no_path_of_ne
    (w := .beta) (v := .eta) (by decide) ⟨p'⟩

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
2-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_2cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point} :
    ¬ Nonempty (KInfinityPath2 p q) := by
  intro h2
  exact betaEtaPaper_witness_interpretations_no_path ⟨p⟩

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
3-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_3cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point}
    {α β : KInfinityPath2 p q} :
    ¬ Nonempty (KInfinityPath3 α β) := by
  intro h3
  exact betaEtaPaper_witness_interpretations_no_2cell ⟨α⟩

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
4-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_4cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β} :
    ¬ Nonempty (KInfinityPath4 η θ) := by
  intro h4
  exact betaEtaPaper_witness_interpretations_no_3cell ⟨η⟩

/-- The packaged β₁ / η₁ witness interpretations also inherit the existing
5-cell separation. -/
theorem betaEtaPaper_witness_interpretations_no_5cell
    {p q : KInfinityPath
      betaEtaPaper_beta1_interpretation.point
      betaEtaPaper_eta1_interpretation.point}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    {ω ξ : KInfinityPath4 η θ} :
    ¬ Nonempty (KInfinityPath5 ω ξ) := by
  intro h5
  exact betaEtaPaper_witness_interpretations_no_4cell ⟨ω⟩

/-- The recursively completed all-dimensional separation also transfers to the
packaged β₁ / η₁ witness interpretations. -/
theorem betaEtaPaper_witness_interpretations_no_recursive_higher_cell
    (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = betaEtaPaper_beta1_interpretation.point ∧
          kInfinityTowerTargetObj x = betaEtaPaper_eta1_interpretation.point} := by
  intro hx
  rcases hx with ⟨x, hs, ht⟩
  have hs' : kInfinityTowerSourceObj x = interp1Beta := by
    simpa using hs
  have ht' : kInfinityTowerTargetObj x = interp1Eta := by
    simpa using ht
  exact Example42DirectWitness.no_recursive_higher_cell_of_ne
    (w := .beta) (v := .eta) (by decide) n ⟨x, hs', ht'⟩

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
whose 0-source/0-target boundary is the chosen β/η pair, because the explicit
5-cells and 6-cells already collapse and every dimension above `6` is obtained
by recursive identity completion. -/
theorem beta_eta_points_no_recursive_higher_cell_in_KInfinity
    (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = interp1Beta ∧
          kInfinityTowerTargetObj x = interp1Eta} :=
  example_4_2_no_recursive_higher_cell_nonempty n

end HigherLambdaModel.KInfinity
