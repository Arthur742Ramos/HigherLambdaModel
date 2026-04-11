import HigherLambdaModel.Lambda.ExtensionalKanCore

namespace HigherLambdaModel.Lambda.ExtensionalKan

open Term HigherTerms

/-!
## Higher semantic / HoTFT layer for extensional Kan complexes.

This module contains the later Section 2 HoTFT API and the large semantic
coherence development, split out of `ExtensionalKan.lean` so edits to the
higher layer do not force recompilation of the simplicial/core interpreter.
-/

/-! ## Homotopy Type-Free Theory (Definition 2.10) -/

/-- Soundness of a single β-step in an extensional Kan complex. -/
theorem betaStep_sound
    (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | beta M N =>
    exact beta_sound K M N ρ
  | appL _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | appR _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | lam _ ih =>
    simp only [interpret]
    congr 1
    funext f
    exact ih (fun n => if n = 0 then f else ρ (n - 1))

/-- Soundness of a single η-step in an extensional Kan complex. -/
theorem etaStep_sound
    (K : ExtensionalKanComplex) (M N : Term)
    (h : EtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | eta M hfv =>
    have h_not_free : Term.hasFreeVar 0 M = false := by
      simp at hfv
      exact hfv
    simp only [interpret, ReflexiveKanComplex.app]
    have key : ∀ f, interpret K.toReflexiveKanComplex
                      (fun n => if n = 0 then f else ρ (n - 1)) M =
                   interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M) := by
      intro f
      exact interpret_unshift K.toReflexiveKanComplex M ρ f h_not_free
    have inner_eq : (fun f => K.F (interpret K.toReflexiveKanComplex
                                     (fun n => if n = 0 then f else ρ (n - 1)) M)
                                   (if True then f else ρ (0 - 1))) =
                    K.F (interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M)) := by
      funext f
      simp only [ite_true, key]
    rw [inner_eq]
    exact (K.epsilon (interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M))).symm
  | appL _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | appR _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | lam _ ih =>
    simp only [interpret]
    congr 1
    funext f
    exact ih (fun n => if n = 0 then f else ρ (n - 1))

/-- Soundness of a single βη-step in an extensional Kan complex. -/
theorem betaEtaStep_sound
    (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaEtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  cases h with
  | beta hb => exact betaStep_sound K M N hb ρ
  | eta he => exact etaStep_sound K M N he ρ

/-- A single forward βη-step induces a semantic 1-conversion. At present this
basic edge is still obtained from equality soundness and is therefore
degenerate; nontrivial path structure enters when longer paths are composed via
`KanComplex.compPath`. -/
noncomputable def betaEtaStep_in_Theory1
    (K : ExtensionalKanComplex) (M N : Term) (h : BetaEtaStep M N) :
    Theory1 K M N :=
  Theory1.ofTheoryEq K (fun ρ => betaEtaStep_sound K M N h ρ)

/-- A single backward βη-step induces a semantic 1-conversion in the reverse
direction. -/
noncomputable def betaEtaStepInv_in_Theory1
    (K : ExtensionalKanComplex) (M N : Term) (h : BetaEtaStep N M) :
    Theory1 K M N :=
  Theory1.ofTheoryEq K (fun ρ => (betaEtaStep_sound K N M h ρ).symm)

/-- Equality-generated semantic 1-cell corresponding to the endpoint equality in
Proposition 2.1. -/
noncomputable def beta_nested_eq_in_Theory1
    (K : ExtensionalKanComplex) (M N P : Term) :
    Theory1 K (M[Term.app (Term.lam N) P]) (M[N[P]]) :=
  Theory1.ofTheoryEq K (fun ρ => beta_nested_compat K.toReflexiveKanComplex M N P ρ)

/-- Proof-relevant refinement of Proposition 2.1 in a fixed extensional Kan
complex: the outer-first and inner-first β-reduction orders for a nested redex
are related by a semantic 2-cell. -/
noncomputable def beta_nested_compat_in_Theory2
    (K : ExtensionalKanComplex) (M N P : Term) :
    Theory2 K
      (Theory1.comp K
        (betaEtaStep_in_Theory1 K _ _
          (BetaEtaStep.beta (BetaStep.beta M (Term.app (Term.lam N) P))))
        (beta_nested_eq_in_Theory1 K M N P))
      (Theory1.comp K
        (betaEtaStep_in_Theory1 K _ _
          (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta N P))))
        (betaEtaStep_in_Theory1 K _ _
          (BetaEtaStep.beta (BetaStep.beta M (N[P]))))) := by
  let hOuter :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P))
        (M[Term.app (Term.lam N) P]) :=
    fun ρ =>
      betaEtaStep_sound K _ _
        (BetaEtaStep.beta (BetaStep.beta M (Term.app (Term.lam N) P))) ρ
  let hLeft :
      TheoryEq K (M[Term.app (Term.lam N) P]) (M[N[P]]) :=
    fun ρ => beta_nested_compat K.toReflexiveKanComplex M N P ρ
  let hInner :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P))
        (Term.app (Term.lam M) (N[P])) :=
    fun ρ =>
      betaEtaStep_sound K _ _
        (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta N P))) ρ
  let hRight :
      TheoryEq K (Term.app (Term.lam M) (N[P])) (M[N[P]]) :=
    fun ρ =>
      betaEtaStep_sound K _ _
        (BetaEtaStep.beta (BetaStep.beta M (N[P]))) ρ
  let hOuterFirst :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P)) (M[N[P]]) :=
    fun ρ => (hOuter ρ).trans (hLeft ρ)
  let hInnerFirst :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P)) (M[N[P]]) :=
    fun ρ => (hInner ρ).trans (hRight ρ)
  have hFinalEq : hOuterFirst = hInnerFirst := by
    funext ρ
    exact Subsingleton.elim _ _
  simpa [beta_nested_eq_in_Theory1, hOuter, hLeft, hInner, hRight, hOuterFirst, hInnerFirst] using
    (Theory2.trans K
      (Theory2.ofTheoryEqTrans K hOuter hLeft)
      (Theory2.trans K
        (Theory2.ofEq K
          (congrArg
            (fun h :
              TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P)) (M[N[P]]) =>
                Theory1.ofTheoryEq K h)
            hFinalEq))
        (Theory2.symm K (Theory2.ofTheoryEqTrans K hInner hRight))))

/-- Every explicit βη path preserves interpretation in every extensional Kan
complex. This connects the proof-relevant higher-path layer directly to the
semantic equality layer. -/
theorem reductionSeq_sound
    (K : ExtensionalKanComplex) {M N : Term}
    (p : ReductionSeq M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction p generalizing ρ with
  | refl _ =>
    rfl
  | step s rest ih =>
    exact (betaEtaStep_sound K _ _ s ρ).trans (ih ρ)
  | stepInv s rest ih =>
    exact (betaEtaStep_sound K _ _ s ρ).symm.trans (ih ρ)

/-- Equality-generated semantic path interpretation of an explicit βη path.
This auxiliary bridge is used internally to compare the structural path
interpretation with the underlying equality semantics. -/
noncomputable def reductionSeq_eq_in_Theory1
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory1 K M N :=
  Theory1.ofTheoryEq K (fun ρ => reductionSeq_sound K p ρ)

/-- Structural semantic path interpretation of an explicit βη path. Single
steps still interpret to degenerate edges, but longer paths are composed using
the Kan-complex horn-filling operation and therefore need not collapse through
proof irrelevance. -/
noncomputable def reductionSeq_in_Theory1
    (K : ExtensionalKanComplex) {M N : Term} :
    ReductionSeq M N → Theory1 K M N
  | .refl M => fun ρ => K.reflPath (interpret K.toReflexiveKanComplex ρ M)
  | .step s rest => fun ρ =>
      Theory1.comp K (betaEtaStep_in_Theory1 K _ _ s) (reductionSeq_in_Theory1 K rest) ρ
  | .stepInv s rest => fun ρ =>
      Theory1.comp K (betaEtaStepInv_in_Theory1 K _ _ s) (reductionSeq_in_Theory1 K rest) ρ

/-- Any two parallel explicit βη paths induce the same equality-generated
semantic 1-conversion in a fixed model. This uses proof irrelevance at the
equality layer. -/
theorem reductionSeq_eq_in_Theory1_eq
    (K : ExtensionalKanComplex) {M N : Term}
    (p q : ReductionSeq M N) :
    reductionSeq_eq_in_Theory1 K p = reductionSeq_eq_in_Theory1 K q := by
  unfold reductionSeq_eq_in_Theory1
  have hproof :
      (fun ρ => reductionSeq_sound K p ρ) =
      (fun ρ => reductionSeq_sound K q ρ) :=
    Subsingleton.elim _ _
  exact congrArg (Theory1.ofTheoryEq K) hproof

/-- Every explicit βη path is structurally homotopic to its equality-generated
semantic interpretation in a fixed model. -/
noncomputable def reductionSeq_in_eq_in_Theory2
    (K : ExtensionalKanComplex) :
    {M N : Term} → (p : ReductionSeq M N) →
      Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_eq_in_Theory1 K p)
  | _, _, .refl M =>
      Theory2.ofEq K (Theory1.refl_eq_ofTheoryEq_refl K M)
  | _, _, .step s rest =>
      Theory2.trans K
        (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_in_eq_in_Theory2 K rest))
        (Theory2.ofTheoryEqTrans K
          (fun ρ => betaEtaStep_sound K _ _ s ρ)
          (fun ρ => reductionSeq_sound K rest ρ))
  | _, _, .stepInv s rest =>
      Theory2.trans K
        (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_in_eq_in_Theory2 K rest))
        (Theory2.ofTheoryEqTrans K
          (fun ρ => (betaEtaStep_sound K _ _ s ρ).symm)
          (fun ρ => reductionSeq_sound K rest ρ))

def HoTFT_eq (M N : Term) : Prop :=
  ∀ (K : ExtensionalKanComplex), TheoryEq K M N

scoped notation:50 M " =_HoTFT " N => HoTFT_eq M N

/-- Proof-relevant HoTFT 1-conversions: every extensional Kan complex supplies
an explicit semantic 1-simplex between the interpretations of the terms. -/
def HoTFT1 (M N : Term) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), Theory1 K M N

/-- Proof-relevant HoTFT 2-conversions between parallel proof-relevant HoTFT
1-conversions. -/
def HoTFT2 {M N : Term} (α β : HoTFT1 M N) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), Theory2 K (α K) (β K)

/-- Composition of proof-relevant HoTFT 1-conversions, modelwise. -/
noncomputable def HoTFT1.comp {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) : HoTFT1 L N :=
  fun K => Theory1.comp K (α K) (β K)

/-- Inversion of proof-relevant HoTFT 1-conversions, modelwise. -/
noncomputable def HoTFT1.inv {M N : Term} (α : HoTFT1 M N) : HoTFT1 N M :=
  fun K => Theory1.inv K (α K)

/-- Reflexivity of proof-relevant HoTFT 1-conversions. -/
noncomputable def HoTFT1.refl (M : Term) : HoTFT1 M M :=
  fun K => Theory1.refl K M

/-- Any equality-level HoTFT fact induces a proof-relevant HoTFT 1-conversion. -/
noncomputable def HoTFT1.ofHoTFTEq {M N : Term} (h : HoTFT_eq M N) : HoTFT1 M N :=
  fun K => Theory1.ofTheoryEq K (h K)

/-- A single forward βη-step induces a proof-relevant HoTFT 1-conversion. -/
noncomputable def betaEtaStep_in_HoTFT1 (M N : Term) (h : BetaEtaStep M N) :
    HoTFT1 M N :=
  fun K => betaEtaStep_in_Theory1 K M N h

/-- A single backward βη-step induces a proof-relevant HoTFT 1-conversion. -/
noncomputable def betaEtaStepInv_in_HoTFT1 (M N : Term) (h : BetaEtaStep N M) :
    HoTFT1 M N :=
  fun K => betaEtaStepInv_in_Theory1 K M N h

/-- Reflexivity of proof-relevant HoTFT 2-conversions. -/
noncomputable def HoTFT2.refl {M N : Term} (α : HoTFT1 M N) : HoTFT2 α α :=
  fun K => Theory2.refl K (α K)

/-- Symmetry of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.symm {M N : Term} {α β : HoTFT1 M N} :
    HoTFT2 α β → HoTFT2 β α
  | η => fun K => Theory2.symm K (η K)

/-- Vertical composition of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.trans {M N : Term} {α β γ : HoTFT1 M N} :
    HoTFT2 α β → HoTFT2 β γ → HoTFT2 α γ
  | η₁, η₂ => fun K => Theory2.trans K (η₁ K) (η₂ K)

/-- Left whiskering of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.whiskerLeft {L M N : Term} (α : HoTFT1 L M)
    {β γ : HoTFT1 M N} :
    HoTFT2 β γ → HoTFT2 (HoTFT1.comp α β) (HoTFT1.comp α γ)
  | η => fun K => Theory2.whiskerLeft K (α K) (η K)

/-- Right whiskering of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.whiskerRight {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp α γ) (HoTFT1.comp β γ) :=
  fun K => Theory2.whiskerRight K (η K) (γ K)

/-- A proof-relevant HoTFT triangle, represented modelwise by semantic
triangles. -/
def HoTFTTriangle {M₀ M₁ M₂ : Term}
    (α01 : HoTFT1 M₀ M₁) (α02 : HoTFT1 M₀ M₂) (α12 : HoTFT1 M₁ M₂) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), TheoryTriangle K (α01 K) (α02 K) (α12 K)

/-- Every HoTFT 2-cell determines a HoTFT triangle with degenerate third
side. -/
noncomputable def HoTFT2.toTriangle {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFTTriangle α β (HoTFT1.refl N) :=
  fun K => Theory2.toTriangle K (η K)

/-- The chosen composition triangle at the HoTFT layer. -/
noncomputable def HoTFT1.compTriangle {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFTTriangle α (HoTFT1.comp α β) β :=
  fun K => Theory1.compTriangle K (α K) (β K)

/-- The chosen source-degenerate triangle at the HoTFT layer. -/
noncomputable def HoTFT1.sourceDegenerateTriangle {M N : Term}
    (α : HoTFT1 M N) :
    HoTFTTriangle (HoTFT1.refl M) α α :=
  fun K => Theory1.sourceDegenerateTriangle K (α K)

/-- The auxiliary HoTFT triangle behind the associator 2-cell. -/
noncomputable def HoTFT1.assocTriangle {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) (γ : HoTFT1 N P) :
    HoTFTTriangle α
      (HoTFT1.comp (HoTFT1.comp α β) γ)
      (HoTFT1.comp β γ) :=
  fun K => Theory1.assocTriangle K (α K) (β K) (γ K)

/-- The auxiliary HoTFT triangle behind right whiskering. -/
noncomputable def HoTFT1.whiskerRightTriangle {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFTTriangle β (HoTFT1.comp α γ) γ :=
  fun K => Theory1.whiskerRightTriangle K (η K) (γ K)

/-- A proof-relevant HoTFT tetrahedron, represented modelwise by semantic
tetrahedra. -/
def HoTFTTetrahedron
    {M₀ M₁ M₂ M₃ : Term}
    {α01 : HoTFT1 M₀ M₁} {α02 : HoTFT1 M₀ M₂} {α03 : HoTFT1 M₀ M₃}
    {α12 : HoTFT1 M₁ M₂} {α13 : HoTFT1 M₁ M₃} {α23 : HoTFT1 M₂ M₃}
    (τ0 : HoTFTTriangle α12 α13 α23)
    (τ1 : HoTFTTriangle α02 α03 α23)
    (τ2 : HoTFTTriangle α01 α03 α13)
    (τ3 : HoTFTTriangle α01 α02 α12) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), TheoryTetrahedron K (τ0 K) (τ1 K) (τ2 K) (τ3 K)

/-- Degenerating a HoTFT triangle along its middle face produces a HoTFT
tetrahedron whose middle face is the reflexive HoTFT 2-cell on that middle
edge. -/
noncomputable def HoTFTTriangle.reflTetrahedron
    {M₀ M₁ M₂ : Term}
    {α01 : HoTFT1 M₀ M₁} {α02 : HoTFT1 M₀ M₂} {α12 : HoTFT1 M₁ M₂}
    (τ : HoTFTTriangle α01 α02 α12) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl α12))
      (HoTFT2.toTriangle (HoTFT2.refl α02))
      τ
      τ :=
  fun K => TheoryTriangle.reflTetrahedron K (τ K)

/-- HoTFT triangle-comparison 2-cell between two HoTFT triangles with common
boundary. -/
noncomputable def HoTFTTriangle.comparisonPath2
    {M₀ M₁ M₂ : Term}
    {α01 : HoTFT1 M₀ M₁} {α02 : HoTFT1 M₀ M₂} {α12 : HoTFT1 M₁ M₂}
    (τ₁ τ₂ : HoTFTTriangle α01 α02 α12) :
    HoTFT2 α02 α02 :=
  fun K => TheoryTriangle.comparisonPath2 K (τ₁ K) (τ₂ K)

/-- HoTFT boundary-aware tetrahedron whose middle face is the comparison
between two HoTFT triangles with common boundary. -/
noncomputable def HoTFTTriangle.comparisonTetrahedron
    {M₀ M₁ M₂ : Term}
    {α01 : HoTFT1 M₀ M₁} {α02 : HoTFT1 M₀ M₂} {α12 : HoTFT1 M₁ M₂}
    (τ₁ τ₂ : HoTFTTriangle α01 α02 α12) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl α12))
      (HoTFT2.toTriangle (HoTFTTriangle.comparisonPath2 τ₁ τ₂))
      τ₂
      τ₁ :=
  fun K => TheoryTriangle.comparisonTetrahedron K (τ₁ K) (τ₂ K)

/-- Horizontal composition of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.hcomp {L M N : Term}
    {α α' : HoTFT1 L M} {β β' : HoTFT1 M N}
    (η : HoTFT2 α α') (θ : HoTFT2 β β') :
    HoTFT2 (HoTFT1.comp α β) (HoTFT1.comp α' β') :=
  HoTFT2.trans
    (HoTFT2.whiskerRight η β)
    (HoTFT2.whiskerLeft α' θ)

/-- Associator for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.associator {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) (γ : HoTFT1 N P) :
    HoTFT2 (HoTFT1.comp (HoTFT1.comp α β) γ)
      (HoTFT1.comp α (HoTFT1.comp β γ)) :=
  fun K => Theory2.associator K (α K) (β K) (γ K)

/-- Right inverse law for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.rightInverse {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp α (HoTFT1.inv α)) (HoTFT1.refl M) :=
  fun K => Theory2.rightInverse K (α K)

/-- Left inverse law for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.leftInverse {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp (HoTFT1.inv α) α) (HoTFT1.refl N) :=
  fun K => Theory2.leftInverse K (α K)

/-- Left unitor for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.leftUnitor {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp (HoTFT1.refl M) α) α :=
  fun K => Theory2.leftUnitor K (α K)

/-- Right unitor for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.rightUnitor {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp α (HoTFT1.refl N)) α :=
  fun K => Theory2.rightUnitor K (α K)

/-- Equality of proof-relevant HoTFT 1-conversions induces a HoTFT 2-conversion. -/
noncomputable def HoTFT2.ofEq {M N : Term} {α β : HoTFT1 M N} (h : α = β) : HoTFT2 α β := by
  cases h
  exact HoTFT2.refl α

/-- HoTFT 1-cell corresponding to the endpoint equality in Proposition 2.1. -/
noncomputable def beta_nested_eq_in_HoTFT1 (M N P : Term) :
    HoTFT1 (M[Term.app (Term.lam N) P]) (M[N[P]]) :=
  fun K => beta_nested_eq_in_Theory1 K M N P

/-- Proof-relevant refinement of Proposition 2.1 in HoTFT: the two β-reduction
orders for a nested redex are related by a HoTFT 2-cell. -/
noncomputable def beta_nested_compat_in_HoTFT2 (M N P : Term) :
    HoTFT2
      (HoTFT1.comp
        (betaEtaStep_in_HoTFT1 _ _
          (BetaEtaStep.beta (BetaStep.beta M (Term.app (Term.lam N) P))))
        (beta_nested_eq_in_HoTFT1 M N P))
      (HoTFT1.comp
        (betaEtaStep_in_HoTFT1 _ _
          (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta N P))))
        (betaEtaStep_in_HoTFT1 _ _
          (BetaEtaStep.beta (BetaStep.beta M (N[P]))))) :=
  fun K => beta_nested_compat_in_Theory2 K M N P

/-- Proof-relevant HoTFT 3-conversions between parallel proof-relevant HoTFT
2-conversions. -/
def HoTFT3 {M N : Term} {α β : HoTFT1 M N} (η θ : HoTFT2 α β) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), Theory3 K (α := α K) (β := β K) (η K) (θ K)

/-- Reflexivity of proof-relevant HoTFT 3-conversions. -/
def HoTFT3.refl {M N : Term} {α β : HoTFT1 M N}
    (η : HoTFT2 α β) : HoTFT3 η η :=
  fun K => Theory3.refl K (η K)

/-- Symmetry of proof-relevant HoTFT 3-conversions. -/
noncomputable def HoTFT3.symm {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β} :
    HoTFT3 η θ → HoTFT3 θ η
  | Γ => fun K => Theory3.symm K (Γ K)

/-- Vertical composition of proof-relevant HoTFT 3-conversions. -/
noncomputable def HoTFT3.trans {M N : Term} {α β : HoTFT1 M N} {η θ ι : HoTFT2 α β} :
    HoTFT3 η θ → HoTFT3 θ ι → HoTFT3 η ι
  | Γ, Δ => fun K => Theory3.trans K (Γ K) (Δ K)

/-- Equality of proof-relevant HoTFT 2-conversions induces a HoTFT
3-conversion. -/
def HoTFT3.ofEq {M N : Term} {α β : HoTFT1 M N}
    {η θ : HoTFT2 α β} (h : η = θ) : HoTFT3 η θ := by
  cases h
  exact HoTFT3.refl η

/-- Two boundary-aware HoTFT tetrahedra with the same outer boundary and a
front face coming from a HoTFT 2-cell induce a proof-relevant HoTFT 3-cell
between their middle faces. -/
noncomputable def HoTFTTetrahedron.path3
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ : HoTFT2 σ τ} {α β : HoTFT2 μ ν}
    {τ2 : HoTFTTriangle ρ ν τ} {τ3 : HoTFTTriangle ρ μ σ}
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle α) τ2 τ3)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle β) τ2 τ3) :
    HoTFT3 α β :=
  fun K => TheoryTetrahedron.path3 K (Ω₁ K) (Ω₂ K)

/-- A proof-relevant HoTFT 3-cell between the front faces of two
boundary-aware HoTFT tetrahedra with identical remaining boundary induces a
proof-relevant HoTFT 3-cell between their middle faces. -/
noncomputable def HoTFTTetrahedron.frontPath3
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ₁ γ₂ : HoTFT2 σ τ} {α β : HoTFT2 μ ν}
    {τ2 : HoTFTTriangle ρ ν τ} {τ3 : HoTFTTriangle ρ μ σ}
    (Κ : HoTFT3 γ₁ γ₂)
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ₁) (HoTFT2.toTriangle α) τ2 τ3)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ₂) (HoTFT2.toTriangle β) τ2 τ3) :
    HoTFT3 α β :=
  fun K => TheoryTetrahedron.frontPath3 K (Κ K) (Ω₁ K) (Ω₂ K)

/-- Dually, two boundary-aware HoTFT tetrahedra with the same middle face and
identical outer boundary induce a proof-relevant HoTFT 3-cell between their
front faces. -/
noncomputable def HoTFTTetrahedron.face0Path3
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ₁ γ₂ : HoTFT2 σ τ} {α : HoTFT2 μ ν}
    {τ2 : HoTFTTriangle ρ ν τ} {τ3 : HoTFTTriangle ρ μ σ}
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ₁) (HoTFT2.toTriangle α) τ2 τ3)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ₂) (HoTFT2.toTriangle α) τ2 τ3) :
    HoTFT3 γ₁ γ₂ :=
  fun K => TheoryTetrahedron.face0Path3 K (Ω₁ K) (Ω₂ K)

/-- A proof-relevant HoTFT 3-cell between the last faces of two
boundary-aware HoTFT tetrahedra with identical front and middle faces induces a
proof-relevant HoTFT 3-cell between their second outer faces. -/
noncomputable def HoTFTTetrahedron.face2Path3
    {M N : Term}
    {α β γ : HoTFT1 M N}
    {η₁ η₂ : HoTFT2 α β} {θ : HoTFT2 β γ}
    {μ₁ μ₂ : HoTFT2 α γ}
    (Κ : HoTFT3 η₁ η₂)
    (Ω₁ : HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle θ)
      (HoTFT2.toTriangle μ₁)
      (HoTFT2.toTriangle η₁))
    (Ω₂ : HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle θ)
      (HoTFT2.toTriangle μ₂)
      (HoTFT2.toTriangle η₂)) :
    HoTFT3 μ₁ μ₂ :=
  fun K => TheoryTetrahedron.face2Path3 K (Κ K) (Ω₁ K) (Ω₂ K)

/-- Conversely, a proof-relevant HoTFT 3-cell between the second outer faces of
two boundary-aware HoTFT tetrahedra with identical front and middle faces
induces a proof-relevant HoTFT 3-cell between their last faces. -/
noncomputable def HoTFTTetrahedron.face3Path3
    {M N : Term}
    {α β γ : HoTFT1 M N}
    {η₁ η₂ : HoTFT2 α β} {θ : HoTFT2 β γ}
    {μ₁ μ₂ : HoTFT2 α γ}
    (Κ : HoTFT3 μ₁ μ₂)
    (Ω₁ : HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle θ)
      (HoTFT2.toTriangle μ₁)
      (HoTFT2.toTriangle η₁))
    (Ω₂ : HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle θ)
      (HoTFT2.toTriangle μ₂)
      (HoTFT2.toTriangle η₂)) :
    HoTFT3 η₁ η₂ :=
  fun K => TheoryTetrahedron.face3Path3 K (Κ K) (Ω₁ K) (Ω₂ K)

/-- A boundary-aware HoTFT 4-simplex comparison between tetrahedra with the
same front face and same second outer face, but potentially different last
outer faces. -/
noncomputable def HoTFTTetrahedron.comparison
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ : HoTFT2 σ τ} {α β : HoTFT2 μ ν} {δ : HoTFT2 μ μ}
    {τ2 : HoTFTTriangle ρ ν τ}
    {τ31 τ32 : HoTFTTriangle ρ μ σ}
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle α) τ2 τ31)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle β) τ2 τ32)
    (Κ : HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl σ))
      (HoTFT2.toTriangle δ)
      τ32 τ31) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle β)
      (HoTFT2.toTriangle α)
      (HoTFT2.toTriangle δ) :=
  fun K => TheoryTetrahedron.comparison K (Ω₁ K) (Ω₂ K) (Κ K)

/-- Interchange at the HoTFT 3-cell layer is immediate from the definition of
modelwise horizontal composition. -/
noncomputable def HoTFT3.interchange {L M N : Term}
    {α α' : HoTFT1 L M} {β β' : HoTFT1 M N}
    (η : HoTFT2 α α') (θ : HoTFT2 β β') :
    HoTFT3 (HoTFT2.hcomp η θ)
      (HoTFT2.trans
        (HoTFT2.whiskerRight η β)
        (HoTFT2.whiskerLeft α' θ)) :=
  HoTFT3.ofEq rfl

/-- Alternative interchange at the HoTFT 3-cell layer. -/
noncomputable def HoTFT3.interchange' {L M N : Term}
    {α α' : HoTFT1 L M} {β β' : HoTFT1 M N}
    (η : HoTFT2 α α') (θ : HoTFT2 β β') :
    HoTFT3 (HoTFT2.hcomp η θ)
      (HoTFT2.trans
        (HoTFT2.whiskerLeft α θ)
        (HoTFT2.whiskerRight η β')) :=
  fun K => Theory3.interchange' K (η K) (θ K)

/-- The boundary-aware tetrahedron whose middle face is the HoTFT semantic
associator 2-cell. -/
noncomputable def HoTFT3.associatorTetrahedron {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) (γ : HoTFT1 N P) :=
  fun K => Theory3.associatorTetrahedron K (α K) (β K) (γ K)

/-- Triangle coherence at the HoTFT semantic 3-cell layer. -/
noncomputable def HoTFT3.triangle {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator α (HoTFT1.refl M) β)
        (HoTFT2.whiskerLeft α (HoTFT2.leftUnitor β)))
      (HoTFT2.whiskerRight (HoTFT2.rightUnitor α) β) :=
  fun K => Theory3.triangle K (α K) (β K)

/-- HoTFT counterpart of `Theory3.rightUnitorComp`. -/
noncomputable def HoTFT3.rightUnitorComp {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator α β (HoTFT1.refl N))
        (HoTFT2.whiskerLeft α (HoTFT2.rightUnitor β)))
      (HoTFT2.rightUnitor (HoTFT1.comp α β)) :=
  fun K => Theory3.rightUnitorComp K (α K) (β K)

/-- HoTFT counterpart of `Theory3.leftUnitorComp`. -/
noncomputable def HoTFT3.leftUnitorComp {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.refl L) α β)
        (HoTFT2.leftUnitor (HoTFT1.comp α β)))
      (HoTFT2.whiskerRight (HoTFT2.leftUnitor α) β) :=
  fun K => Theory3.leftUnitorComp K (α K) (β K)

/-- HoTFT counterpart of `Theory3.leftUnitorNaturality`. -/
noncomputable def HoTFT3.leftUnitorNaturality {L M : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.whiskerLeft (HoTFT1.refl L) η)
        (HoTFT2.leftUnitor β))
      (HoTFT2.trans (HoTFT2.leftUnitor α) η) :=
  fun K => Theory3.leftUnitorNaturality K (η K)

/-- HoTFT counterpart of `Theory3.reflUnitors`. -/
noncomputable def HoTFT3.reflUnitors {M : Term} :
    HoTFT3
      (HoTFT2.leftUnitor (HoTFT1.refl M))
      (HoTFT2.rightUnitor (HoTFT1.refl M)) :=
  fun K => Theory3.reflUnitors K (M := M)

/-- The boundary-aware tetrahedron whose middle face is left whiskering at the
HoTFT semantic layer. -/
noncomputable def HoTFT3.whiskerLeftTetrahedron {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N} (η : HoTFT2 β γ) :=
  fun K => Theory3.whiskerLeftTetrahedron K (α K) (η K)

/-- Left whiskering is congruent on HoTFT 3-cells. -/
noncomputable def HoTFT3.whiskerLeftCongr {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    {η θ : HoTFT2 β γ} (Κ : HoTFT3 η θ) :
    HoTFT3 (HoTFT2.whiskerLeft α η) (HoTFT2.whiskerLeft α θ) :=
  fun K => Theory3.whiskerLeftCongr K (α K) (Κ K)

/-- Left whiskering preserves reflexive HoTFT 2-cells up to proof-relevant
HoTFT 3-cells. -/
noncomputable def HoTFT3.whiskerLeftRefl {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFT3 (HoTFT2.whiskerLeft α (HoTFT2.refl β))
      (HoTFT2.refl (HoTFT1.comp α β)) :=
  fun K => Theory3.whiskerLeftRefl K (α K) (β K)

/-- Left whiskering of an equality-generated HoTFT 2-cell agrees with the
equality-generated whisker on HoTFT 1-cells. -/
noncomputable def HoTFT3.whiskerLeftOfEq {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N} (h : β = γ) :
    HoTFT3 (HoTFT2.whiskerLeft α (HoTFT2.ofEq h))
      (HoTFT2.ofEq (congrArg (fun δ => HoTFT1.comp α δ) h)) :=
  by
    cases h
    simpa using HoTFT3.whiskerLeftRefl α β

/-- HoTFT counterpart of `Theory3.whiskerLeftCongrOfEq`. -/
noncomputable def HoTFT3.whiskerLeftCongrOfEq {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    {η : HoTFT2 β γ} (h : β = γ) :
    HoTFT3 η (HoTFT2.ofEq h) →
      HoTFT3 (HoTFT2.whiskerLeft α η)
        (HoTFT2.ofEq (congrArg (fun δ => HoTFT1.comp α δ) h))
  | Κ => HoTFT3.trans (HoTFT3.whiskerLeftCongr α Κ) (HoTFT3.whiskerLeftOfEq α h)

/-- Left whiskering commutes with vertical composition up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerLeftTrans {L M N : Term}
    (α : HoTFT1 L M) {β γ δ : HoTFT1 M N}
    (η : HoTFT2 β γ) (θ : HoTFT2 γ δ) :
    HoTFT3
      (HoTFT2.whiskerLeft α (HoTFT2.trans η θ))
      (HoTFT2.trans (HoTFT2.whiskerLeft α η) (HoTFT2.whiskerLeft α θ)) :=
  fun K => Theory3.whiskerLeftTrans K (α K) (η K) (θ K)

/-- HoTFT counterpart of `Theory3.whiskerLeftCompFromTriangleComparison`. -/
noncomputable def HoTFT3.whiskerLeftComp
    {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) {γ δ : HoTFT1 N P}
    (η : HoTFT2 γ δ) :
    HoTFT3
      (HoTFT2.whiskerLeft (HoTFT1.comp α β) η)
      (HoTFT2.trans
        (HoTFT2.associator α β γ)
        (HoTFT2.trans
          (HoTFT2.whiskerLeft α (HoTFT2.whiskerLeft β η))
          (HoTFT2.symm (HoTFT2.associator α β δ)))) :=
  fun K => Theory3.whiskerLeftComp K (α K) (β K) (η K)

/-- HoTFT counterpart of `Theory3.whiskerLeftCompFromTriangleComparison`. -/
noncomputable def HoTFT3.whiskerLeftCompFromTriangleComparison
    {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) {γ δ : HoTFT1 N P}
    (η : HoTFT2 γ δ)
    (hTri :
      HoTFT3
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α K ρ) (β K ρ) (γ K ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (K.toReflexiveKanComplex.toKanComplex.compPath
                (α K ρ) (β K ρ))
              (η K ρ)).toTriangle)
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α K ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (β K ρ) (η K ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α K ρ) (β K ρ) (δ K ρ))))) :
    HoTFT3
      (HoTFT2.whiskerLeft (HoTFT1.comp α β) η)
      (HoTFT2.trans
        (HoTFT2.associator α β γ)
        (HoTFT2.trans
          (HoTFT2.whiskerLeft α (HoTFT2.whiskerLeft β η))
          (HoTFT2.symm (HoTFT2.associator α β δ)))) :=
  fun K => Theory3.whiskerLeftCompFromTriangleComparison K
    (α K) (β K) (η K) (hTri K)

/-- HoTFT counterpart of `Theory3.whiskerLeftWhiskerRightFromTriangleComparison`. -/
noncomputable def HoTFT3.whiskerLeftWhiskerRightFromTriangleComparison
    {L M N P : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    (η : HoTFT2 β γ) (δ : HoTFT1 N P)
    (hTri :
      HoTFT3
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α K ρ) (β K ρ) (δ K ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α K ρ) (η K ρ))
              (δ K ρ)).toTriangle)
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α K ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η K ρ) (δ K ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α K ρ) (γ K ρ) (δ K ρ))))) :
    HoTFT3
      (HoTFT2.whiskerRight (HoTFT2.whiskerLeft α η) δ)
      (HoTFT2.trans
        (HoTFT2.associator α β δ)
        (HoTFT2.trans
          (HoTFT2.whiskerLeft α (HoTFT2.whiskerRight η δ))
          (HoTFT2.symm (HoTFT2.associator α γ δ)))) :=
  fun K => Theory3.whiskerLeftWhiskerRightFromTriangleComparison K
    (α K) (η K) (δ K) (hTri K)

/-- Left whiskering commutes with symmetry up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerLeftSymm {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    (η : HoTFT2 β γ) :
    HoTFT3
      (HoTFT2.whiskerLeft α (HoTFT2.symm η))
      (HoTFT2.symm (HoTFT2.whiskerLeft α η)) :=
  fun K => Theory3.whiskerLeftSymm K (α K) (η K)

/-- The inverse direction of left-whisker symmetry at the HoTFT semantic
layer. -/
noncomputable def HoTFT3.invWhiskerLeft {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    (η : HoTFT2 β γ) :
    HoTFT3
      (HoTFT2.symm (HoTFT2.whiskerLeft α η))
      (HoTFT2.whiskerLeft α (HoTFT2.symm η)) :=
  HoTFT3.symm (HoTFT3.whiskerLeftSymm α η)

/-- Right whiskering commutes with vertical composition up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerRightTrans {L M N : Term}
    {α β δ : HoTFT1 L M} (η : HoTFT2 α β) (θ : HoTFT2 β δ)
    (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.whiskerRight (HoTFT2.trans η θ) γ)
      (HoTFT2.trans
        (HoTFT2.whiskerRight η γ)
        (HoTFT2.whiskerRight θ γ)) :=
  fun K => Theory3.whiskerRightTrans K (η K) (θ K) (γ K)

/-- Right whiskering commutes with symmetry up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerRightSymm {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.whiskerRight (HoTFT2.symm η) γ)
      (HoTFT2.symm (HoTFT2.whiskerRight η γ)) :=
  fun K => Theory3.whiskerRightSymm K (η K) (γ K)

/-- The inverse direction of right-whisker symmetry at the HoTFT semantic
layer. -/
noncomputable def HoTFT3.invWhiskerRight {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.symm (HoTFT2.whiskerRight η γ))
      (HoTFT2.whiskerRight (HoTFT2.symm η) γ) :=
  HoTFT3.symm (HoTFT3.whiskerRightSymm η γ)

/-- Right whiskering preserves reflexive HoTFT 2-cells up to HoTFT 3-cells. -/
noncomputable def HoTFT3.whiskerRightRefl {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFT3 (HoTFT2.whiskerRight (HoTFT2.refl α) β)
      (HoTFT2.refl (HoTFT1.comp α β)) :=
  fun K => Theory3.whiskerRightRefl K (α K) (β K)

/-- Right whiskering of an equality-generated HoTFT 2-cell agrees with the
equality-generated whiskered HoTFT 2-cell. -/
noncomputable def HoTFT3.whiskerRightOfEq {L M N : Term}
    {α β : HoTFT1 L M} (h : α = β) (γ : HoTFT1 M N) :
    HoTFT3 (HoTFT2.whiskerRight (HoTFT2.ofEq h) γ)
      (HoTFT2.ofEq (congrArg (fun δ => HoTFT1.comp δ γ) h)) := by
  cases h
  exact HoTFT3.whiskerRightRefl α γ

/-- HoTFT counterpart of `Theory3.whiskerRightCongr`. -/
noncomputable def HoTFT3.whiskerRightCongr {L M N : Term}
    {α β : HoTFT1 L M} {η θ : HoTFT2 α β}
    (Κ : HoTFT3 η θ) (γ : HoTFT1 M N) :
    HoTFT3 (HoTFT2.whiskerRight η γ) (HoTFT2.whiskerRight θ γ) :=
  fun K => Theory3.whiskerRightCongr K (Κ K) (γ K)

/-- The boundary-aware tetrahedron whose middle face is right whiskering at the
HoTFT semantic layer. -/
noncomputable def HoTFT3.whiskerRightTetrahedron {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :=
  fun K => Theory3.whiskerRightTetrahedron K (η K) (γ K)

/-- HoTFT counterpart of `Theory3.whiskerRightComparisonTetrahedron`. -/
noncomputable def HoTFT3.whiskerRightComparisonTetrahedron
    {L M N : Term} {α β : HoTFT1 L M}
    (η θ : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle (HoTFT2.whiskerRight θ γ))
      (HoTFT2.toTriangle (HoTFT2.whiskerRight η γ))
      (HoTFT2.toTriangle
        (HoTFTTriangle.comparisonPath2
          (HoTFT1.whiskerRightTriangle η γ)
          (HoTFT1.whiskerRightTriangle θ γ))) :=
  fun K => Theory3.whiskerRightComparisonTetrahedron K (η K) (θ K) (γ K)

/-- HoTFT counterpart of `Theory3.whiskerRightCongrOfTriangleComparisonPath3`.

If the triangle comparison between the right-whiskered filler triangles of two
parallel HoTFT 2-cells contracts to reflexivity, then right whiskering those
2-cells by the same 1-cell yields a HoTFT 3-cell between the whiskered results.
-/
noncomputable def HoTFT3.whiskerRightCongrOfTriangleComparisonPath3
    {L M N : Term} {α β : HoTFT1 L M} {η θ : HoTFT2 α β}
    (γ : HoTFT1 M N)
    (triangleComparison :
      HoTFT3
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            ((HoTFT1.whiskerRightTriangle η γ) K ρ)
            ((HoTFT1.whiskerRightTriangle θ γ) K ρ))
        (HoTFT2.refl (HoTFT1.comp α γ))) :
    HoTFT3 (HoTFT2.whiskerRight η γ) (HoTFT2.whiskerRight θ γ) :=
  fun K => Theory3.whiskerRightCongrOfTriangleComparisonPath3 K
    (γ K) (triangleComparison K)

/-- HoTFT counterpart of `Theory3.triangleComparisonPath3OfWhiskerRightPath3`.

A HoTFT 3-cell between right-whiskered HoTFT 2-cells contracts the comparison
between their right-whiskered filler triangles. -/
noncomputable def HoTFT3.triangleComparisonPath3OfWhiskerRightPath3
    {L M N : Term} {α β : HoTFT1 L M} {η θ : HoTFT2 α β}
    (γ : HoTFT1 M N)
    (κ : HoTFT3 (HoTFT2.whiskerRight η γ) (HoTFT2.whiskerRight θ γ)) :
    HoTFT3
      (fun K ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          ((HoTFT1.whiskerRightTriangle η γ) K ρ)
          ((HoTFT1.whiskerRightTriangle θ γ) K ρ))
      (HoTFT2.refl (HoTFT1.comp α γ)) :=
  fun K => Theory3.triangleComparisonPath3OfWhiskerRightPath3 K
    (γ K) (κ K)

/-- The boundary-aware tetrahedron whose middle face is the HoTFT semantic
left unitor 2-cell. -/
noncomputable def HoTFT3.leftUnitorTetrahedron {M N : Term}
    (α : HoTFT1 M N) :=
  fun K => Theory3.leftUnitorTetrahedron K (α K)

/-- The boundary-aware tetrahedron whose middle face is the HoTFT semantic
right unitor 2-cell. -/
noncomputable def HoTFT3.rightUnitorTetrahedron {M N : Term}
    (α : HoTFT1 M N) :=
  fun K => Theory3.rightUnitorTetrahedron K (α K)

/-- The boundary-aware tetrahedron filled by the HoTFT semantic vertical
composition operation. Its second outer face is the composite HoTFT 2-cell,
while the original right and left factors remain explicit on the boundary. -/
noncomputable def HoTFT3.transFillerTetrahedron {M N : Term}
    {α β γ : HoTFT1 M N} (η : HoTFT2 α β) (θ : HoTFT2 β γ) :=
  fun K => Theory3.transFillerTetrahedron K (η K) (θ K)

/-- Vertical composition of HoTFT 2-cells is congruent in its left argument up
to HoTFT 3-cells. -/
noncomputable def HoTFT3.transCongrLeft {M N : Term}
    {α β γ : HoTFT1 M N} {η₁ η₂ : HoTFT2 α β}
    (Κ : HoTFT3 η₁ η₂) (θ : HoTFT2 β γ) :
    HoTFT3 (HoTFT2.trans η₁ θ) (HoTFT2.trans η₂ θ) :=
  fun K => Theory3.transCongrLeft K (Κ K) (θ K)

/-- Vertical composition of HoTFT 2-cells is congruent in its right argument up
to HoTFT 3-cells. -/
noncomputable def HoTFT3.transCongrRight {M N : Term}
    {α β γ : HoTFT1 M N} (η : HoTFT2 α β)
    {θ₁ θ₂ : HoTFT2 β γ} (Κ : HoTFT3 θ₁ θ₂) :
    HoTFT3 (HoTFT2.trans η θ₁) (HoTFT2.trans η θ₂) :=
  fun K => Theory3.transCongrRight K (η K) (Κ K)

/-- Vertical composition with a reflexive left factor normalizes to the right
factor at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transReflLeft {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans (HoTFT2.refl α) η) η :=
  fun K => Theory3.transReflLeft K (η K)

/-- Vertical composition with a reflexive right factor normalizes to the left
factor at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transReflRight {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans η (HoTFT2.refl β)) η :=
  fun K => Theory3.transReflRight K (η K)

/-- Right composition with a 2-cell followed by its inverse yields the reflexive
2-cell at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transRightCancel {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans η (HoTFT2.symm η)) (HoTFT2.refl α) :=
  fun K => Theory3.transRightCancel K (η K)

/-- Left composition with the inverse of a 2-cell yields the reflexive target
2-cell at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transLeftCancel {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans (HoTFT2.symm η) η) (HoTFT2.refl β) :=
  fun K => Theory3.transLeftCancel K (η K)

/-- A HoTFT 3-cell between parallel HoTFT 2-cells contracts the triangle
comparison between their associated triangles. -/
noncomputable def HoTFT3.triangleComparisonPath3OfPath3 {M N : Term}
    {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    (Κ : HoTFT3 η θ) :
    HoTFT3
      (fun K ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          ((η K ρ).toTriangle) ((θ K ρ).toTriangle))
      (HoTFT2.refl β) :=
  fun K => Theory3.triangleComparisonPath3OfPath3 K (Κ K)

/-- HoTFT counterpart of `Theory3.whiskerRightLeftCancel`. -/
noncomputable def HoTFT3.whiskerRightLeftCancel {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.whiskerRight (HoTFT2.symm η) γ)
        (HoTFT2.whiskerRight η γ))
      (HoTFT2.refl (HoTFT1.comp β γ)) :=
  fun K => Theory3.whiskerRightLeftCancel K (η K) (γ K)

/-- Vertical composition of HoTFT 2-cells is associative up to a HoTFT 3-cell. -/
noncomputable def HoTFT3.transAssoc {M N : Term}
    {α β γ δ : HoTFT1 M N}
    (η : HoTFT2 α β) (θ : HoTFT2 β γ) (ι : HoTFT2 γ δ) :
    HoTFT3
      (HoTFT2.trans (HoTFT2.trans η θ) ι)
      (HoTFT2.trans η (HoTFT2.trans θ ι)) :=
  fun K => Theory3.transAssoc K (η K) (θ K) (ι K)

/-- The symmetry of a HoTFT vertical composite agrees with the composite of the
symmetries of its factors in reverse order, up to a HoTFT 3-cell. -/
noncomputable def HoTFT3.symmTrans {M N : Term}
    {α β γ : HoTFT1 M N} (η : HoTFT2 α β) (θ : HoTFT2 β γ) :
    HoTFT3 (HoTFT2.symm (HoTFT2.trans η θ))
      (HoTFT2.trans (HoTFT2.symm θ) (HoTFT2.symm η)) :=
  fun K => Theory3.symmTrans K (η K) (θ K)

/-- Right-cancel a common HoTFT right factor from a HoTFT 3-cell between two
composites. -/
noncomputable def HoTFT3.transRightCancelCongr {M N : Term}
    {α β γ : HoTFT1 M N} {η₁ η₂ : HoTFT2 α β} (θ : HoTFT2 β γ) :
    HoTFT3 (HoTFT2.trans η₁ θ) (HoTFT2.trans η₂ θ) → HoTFT3 η₁ η₂
  | Κ => fun K => Theory3.transRightCancelCongr K (θ K) (Κ K)

/-- Symmetry is congruent on HoTFT 3-cells. -/
noncomputable def HoTFT3.symmCongr {M N : Term}
    {α β : HoTFT1 M N} {η θ : HoTFT2 α β} :
    HoTFT3 η θ → HoTFT3 (HoTFT2.symm η) (HoTFT2.symm θ)
  | Κ => fun K => Theory3.symmCongr K (Κ K)

/-- Double symmetry on a HoTFT 2-cell contracts back to the original 2-cell up
to a HoTFT 3-cell. -/
noncomputable def HoTFT3.symmSymm {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.symm (HoTFT2.symm η)) η :=
  fun K => Theory3.symmSymm K (η K)

/-- Proof-relevant HoTFT 4-conversions between parallel proof-relevant HoTFT
3-conversions. -/
def HoTFT4 {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    (Γ Δ : HoTFT3 η θ) : Sort _ :=
  ∀ (K : ExtensionalKanComplex),
    Theory4 K (α := α K) (β := β K) (η := η K) (θ := θ K) (Γ K) (Δ K)

/-- Reflexivity of proof-relevant HoTFT 4-conversions. -/
def HoTFT4.refl {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    (Γ : HoTFT3 η θ) : HoTFT4 Γ Γ :=
  fun K => Theory4.refl K (Γ K)

/-- Equality of proof-relevant HoTFT 3-conversions induces a HoTFT
4-conversion. -/
def HoTFT4.ofEq {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    {Γ Δ : HoTFT3 η θ} (h : Γ = Δ) : HoTFT4 Γ Δ := by
  cases h
  exact HoTFT4.refl Γ

/-- Every explicit βη path induces HoTFT equality between its endpoints. -/
theorem reductionSeq_in_HoTFT {M N : Term} (p : ReductionSeq M N) :
    HoTFT_eq M N := by
  intro K ρ
  exact reductionSeq_sound K p ρ

/-- Every explicit βη path induces a proof-relevant HoTFT 1-conversion by
recursively composing semantic step edges via horn fillers. -/
noncomputable def reductionSeq_in_HoTFT1 {M N : Term} (p : ReductionSeq M N) :
    HoTFT1 M N :=
  fun K => reductionSeq_in_Theory1 K p

/-- The semantic inverse of the structural 1-cell induced by an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_inv_in_Theory1
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory1 K N M :=
  Theory1.inv K (reductionSeq_in_Theory1 K p)

/-- The semantic inverse of the structural HoTFT 1-cell induced by an explicit
βη path. -/
noncomputable def reductionSeq_inv_in_HoTFT1
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT1 N M :=
  HoTFT1.inv (reductionSeq_in_HoTFT1 p)

/-- Structural left whiskering of a semantic 2-cell along an explicit βη path
in a fixed model. This is the semantic operation matching the syntactic
`Homotopy2.whiskerLeft` constructor. -/
noncomputable def reductionSeq_whiskerLeft_in_Theory2
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) →
        Theory2 K (reductionSeq_in_Theory1 K (ReductionSeq.concat r p))
          (reductionSeq_in_Theory1 K (ReductionSeq.concat r q))
  | _, _, _, .refl _, _, _, η => η
  | _, _, _, .step s rest, _, _, η =>
      Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeft_in_Theory2 K rest η)
  | _, _, _, .stepInv s rest, _, _, η =>
      Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeft_in_Theory2 K rest η)

/-- Structural left whiskering along an explicit βη path is congruent on
semantic 3-cells. -/
noncomputable def reductionSeq_whiskerLeftCongr_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      {η θ : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)} →
      Theory3 K η θ →
        Theory3 K (reductionSeq_whiskerLeft_in_Theory2 K r η)
          (reductionSeq_whiskerLeft_in_Theory2 K r θ)
  | _, _, _, .refl _, _, _, _, _, Κ => Κ
  | _, _, _, .step s rest, _, _, _, _, Κ =>
      Theory3.whiskerLeftCongr K (betaEtaStep_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeftCongr_in_Theory3 K rest Κ)
  | _, _, _, .stepInv s rest, _, _, _, _, Κ =>
      Theory3.whiskerLeftCongr K (betaEtaStepInv_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeftCongr_in_Theory3 K rest Κ)

/-- Structural left whiskering along an explicit βη path commutes with vertical
composition up to semantic 3-cells. -/
noncomputable def reductionSeq_whiskerLeftTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term} (r : ReductionSeq L M)
    {p q s : ReductionSeq M N}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (θ : Theory2 K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K s)) :
    Theory3 K
      (reductionSeq_whiskerLeft_in_Theory2 K r (Theory2.trans K η θ))
      (Theory2.trans K (reductionSeq_whiskerLeft_in_Theory2 K r η)
        (reductionSeq_whiskerLeft_in_Theory2 K r θ)) := by
  induction r with
  | refl _ =>
      exact Theory3.refl K (Theory2.trans K η θ)
  | step t rest ih =>
      exact Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStep_in_Theory1 K _ _ t)
          (ih η θ))
        (Theory3.whiskerLeftTrans K (betaEtaStep_in_Theory1 K _ _ t)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η)
          (reductionSeq_whiskerLeft_in_Theory2 K rest θ))
  | stepInv t rest ih =>
      exact Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStepInv_in_Theory1 K _ _ t)
          (ih η θ))
        (Theory3.whiskerLeftTrans K (betaEtaStepInv_in_Theory1 K _ _ t)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η)
          (reductionSeq_whiskerLeft_in_Theory2 K rest θ))

/-- Structural left whiskering along an explicit βη path commutes with symmetry
up to semantic 3-cells. -/
noncomputable def reductionSeq_whiskerLeftSymm_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)) →
        Theory3 K
          (reductionSeq_whiskerLeft_in_Theory2 K r (Theory2.symm K η))
          (Theory2.symm K (reductionSeq_whiskerLeft_in_Theory2 K r η))
  | _, _, _, .refl _, _, _, η =>
      Theory3.refl K (Theory2.symm K η)
  | _, _, _, .step s rest, _, _, η =>
      Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeftSymm_in_Theory3 K rest η))
        (Theory3.whiskerLeftSymm K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η))
  | _, _, _, .stepInv s rest, _, _, η =>
      Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeftSymm_in_Theory3 K rest η))
        (Theory3.whiskerLeftSymm K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η))

/-- Structural comparison between semantic composition of interpreted explicit
βη paths and interpretation of their syntactic concatenation. -/
noncomputable def reductionSeq_comp_in_Theory2
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      Theory2 K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
        (reductionSeq_in_Theory1 K (ReductionSeq.concat p q))
  | _, _, _, .refl _, q =>
      Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
  | _, _, _, .step s rest, q =>
      Theory2.trans K
        (Theory2.associator K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_in_Theory1 K rest) (reductionSeq_in_Theory1 K q))
        (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_comp_in_Theory2 K rest q))
  | _, _, _, .stepInv s rest, q =>
      Theory2.trans K
        (Theory2.associator K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_in_Theory1 K rest) (reductionSeq_in_Theory1 K q))
        (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_comp_in_Theory2 K rest q))

/-- Generic structural right whiskering of a semantic 2-cell along an explicit
βη path in a fixed model.

The full and structural 2-cell interpreters special-case reflexive input and
use the normalized semantic whisker directly. This helper remains the generic
shell used for non-reflexive right whiskering. -/
noncomputable def reductionSeq_whiskerRight_in_Theory2
    (K : ExtensionalKanComplex) {L M N : Term} {p q : ReductionSeq L M}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (s : ReductionSeq M N) :
    Theory2 K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))
      (reductionSeq_in_Theory1 K (ReductionSeq.concat q s)) :=
  Theory2.trans K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K p s))
    (Theory2.trans K
      (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K s))
      (reductionSeq_comp_in_Theory2 K q s))

/-- Structural-endpoint shell for the normalized semantic left whisker. The outer
endpoints stay on `reductionSeq_in_Theory1`, while the middle of the shell
passes through the normalized semantic left whisker and the structural
comparison cells for the source and target explicit composites. -/
noncomputable def reductionSeq_whiskerLeft_shell_in_Theory2
    (K : ExtensionalKanComplex) {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)) :
    Theory2 K (reductionSeq_in_Theory1 K (ReductionSeq.concat r p))
      (reductionSeq_in_Theory1 K (ReductionSeq.concat r q)) :=
  Theory2.trans K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K r p))
    (Theory2.trans K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) η)
      (reductionSeq_comp_in_Theory2 K r q))

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
semantic 2-conversion between the corresponding structural semantic 1-cells in
a fixed extensional Kan complex. -/
noncomputable def homotopy2Deriv_in_Theory2
    (K : ExtensionalKanComplex) :
    {M N : Term} → {p q : ReductionSeq M N} →
      Homotopy2Deriv p q →
        Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)
  | _, _, _, _, .refl p => Theory2.refl K (reductionSeq_in_Theory1 K p)
  | _, _, _, _, .ofEq h =>
      Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h)
  | _, _, _, _, .symm α =>
      Theory2.symm K (homotopy2Deriv_in_Theory2 K α)
  | _, _, _, _, .trans α β =>
      Theory2.trans K (homotopy2Deriv_in_Theory2 K α) (homotopy2Deriv_in_Theory2 K β)
  | _, _, _, _, .diamond p₁ p₂ q₁ q₂ =>
      let c₁ := ReductionSeq.concat p₁ q₁
      let c₂ := ReductionSeq.concat p₂ q₂
      Theory2.trans K
        (reductionSeq_in_eq_in_Theory2 K c₁)
        (Theory2.trans K
          (Theory2.ofEq K (reductionSeq_eq_in_Theory1_eq K c₁ c₂))
          (Theory2.symm K (reductionSeq_in_eq_in_Theory2 K c₂)))
  | _, _, _, _, .whiskerLeft r α =>
      reductionSeq_whiskerLeft_in_Theory2 K r (homotopy2Deriv_in_Theory2 K α)
  | _, _, _, _, .whiskerRight (.refl p) s =>
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))
  | _, _, _, _, .whiskerRight α s =>
      reductionSeq_whiskerRight_in_Theory2 K (homotopy2Deriv_in_Theory2 K α) s

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
semantic 2-conversion between the corresponding structural semantic 1-cells in
a fixed extensional Kan complex. -/
noncomputable def homotopy2_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) :=
  homotopy2Deriv_in_Theory2 K α.deriv

/-- Interpreting an equality-generated syntactic 2-cell is exactly the
corresponding equality-generated semantic 2-cell. -/
theorem homotopy2_in_Theory2_ofEq
    (K : ExtensionalKanComplex) {M N : Term} {p q : ReductionSeq M N}
    (h : p = q) :
    homotopy2_in_Theory2 K (HigherTerms.Homotopy2.ofEq h) =
      Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h) := by
  cases h
  rfl

/-- Interpreting a syntactic reflexive 2-cell in a fixed model is
definitionally the reflexive semantic 2-cell on the interpreted path. -/
theorem homotopy2_in_Theory2_refl
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    homotopy2_in_Theory2 K (Homotopy2.refl p) =
      Theory2.refl K (reductionSeq_in_Theory1 K p) :=
  rfl

/-- Interpreting an equality-generated syntactic left whisker unfolds
definitionally to the corresponding structural left-whisker shell. -/
theorem homotopy2_in_Theory2_whiskerLeft_ofEq
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (h : p = q) :
    homotopy2_in_Theory2 K (whiskerLeft r (HigherTerms.Homotopy2.ofEq h)) =
      reductionSeq_whiskerLeft_in_Theory2 K r
        (Theory2.ofEq K (congrArg (fun t => reductionSeq_in_Theory1 K t) h)) := by
  cases h
  rfl

/-- Interpreting a reflexive syntactic right whisker in a fixed model unfolds
definitionally to the reflexive semantic 2-cell on the interpreted
concatenation. -/
theorem homotopy2_in_Theory2_whiskerRight_refl
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_Theory2 K (whiskerRight (Homotopy2.refl p) s) =
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s)) :=
  rfl

/-- Interpreting an equality-generated syntactic right whisker unfolds
definitionally to the corresponding structural right-whisker shell. -/
theorem homotopy2_in_Theory2_whiskerRight_ofEq
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (h : p = q) (s : ReductionSeq M N) :
    homotopy2_in_Theory2 K (whiskerRight (HigherTerms.Homotopy2.ofEq h) s) =
      reductionSeq_whiskerRight_in_Theory2 K
        (Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h)) s :=
  by
    cases h
    rfl

/-- Semantic 3-cell packaging the definitional bridge from the interpreted
syntactic `whiskerRight` reflexivity source to the reflexive semantic source on
the interpreted concatenation. -/
noncomputable def homotopy2_whiskerRight_refl_source_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (whiskerRight (Homotopy2.refl p) s))
      (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))) :=
  Theory3.ofEq K (homotopy2_in_Theory2_whiskerRight_refl K p s)

/-- Interpreting the reflexive syntactic 2-cell on a concatenated path is
definitionally the reflexive semantic 2-cell on the interpreted concatenation. -/
theorem homotopy2_in_Theory2_refl_concat
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_Theory2 K (Homotopy2.refl (ReductionSeq.concat p s)) =
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s)) :=
  rfl

/-- Semantic 3-cell packaging the definitional bridge from the interpreted
syntactic reflexive target of `whiskerRightRefl` to the structural semantic
reflexive target on the concatenated path. -/
noncomputable def homotopy2_refl_concat_target_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (Homotopy2.refl (ReductionSeq.concat p s)))
      (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))) :=
  Theory3.ofEq K (homotopy2_in_Theory2_refl_concat K p s)

/-- Every explicit syntactic 2-cell admits a reflexive semantic 3-cell over
its interpreted semantic 2-cell in a fixed model. -/
noncomputable def homotopy2_refl_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K α) :=
  Theory3.refl K (homotopy2_in_Theory2 K α)

/-- Equality of explicit syntactic 2-cells induces a semantic 3-cell between
their interpreted semantic 2-cells in a fixed model. -/
noncomputable def homotopy2_eq_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} {α β : Homotopy2 p q} (h : α = β) :
    Theory3 K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β) :=
  Theory3.ofEq K (congrArg (fun γ => homotopy2_in_Theory2 K γ) h)

/-- The semantic image of syntactic interchange is already a semantic 3-cell in
the current simplicial layer because semantic horizontal composition is defined
by the corresponding whiskering composite. -/
noncomputable def homotopy2_interchange_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Theory3 K
      (Theory2.hcomp K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β))
      (Theory2.trans K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K q))
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p') (homotopy2_in_Theory2 K β))) :=
  Theory3.interchange K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)

/-- Alternative interchange on interpreted explicit 2-cells at the semantic
3-cell layer. -/
noncomputable def homotopy2_interchange'_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Theory3 K
      (Theory2.hcomp K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β))
      (Theory2.trans K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) (homotopy2_in_Theory2 K β))
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K q'))) :=
  Theory3.interchange' K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)

/-- Reflexivity of the structural semantic 2-cell associated to an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_refl_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K p) :=
  Theory2.refl K (reductionSeq_in_Theory1 K p)

/-- Associator for semantic composition of the structural 1-cells induced by
explicit βη paths in a fixed model. -/
noncomputable def reductionSeq_associator_in_Theory2
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory2 K
      (Theory1.comp K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
        (reductionSeq_in_Theory1 K r))
      (Theory1.comp K
        (reductionSeq_in_Theory1 K p)
        (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))) :=
  Theory2.associator K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)

/-- Right inverse law for the semantic 1-cell induced by an explicit βη path in
a fixed model. -/
noncomputable def reductionSeq_rightInverse_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_inv_in_Theory1 K p))
      (Theory1.refl K M) :=
  Theory2.rightInverse K (reductionSeq_in_Theory1 K p)

/-- Left inverse law for the semantic 1-cell induced by an explicit βη path in
a fixed model. -/
noncomputable def reductionSeq_leftInverse_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (reductionSeq_inv_in_Theory1 K p) (reductionSeq_in_Theory1 K p))
      (Theory1.refl K N) :=
  Theory2.leftInverse K (reductionSeq_in_Theory1 K p)

/-- Symmetry of the structural semantic 2-cell associated to explicit βη
paths in a fixed model. -/
noncomputable def reductionSeq_symm_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} {p q : ReductionSeq M N} :
    Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) →
      Theory2 K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K p)
  | η => Theory2.symm K η

/-- Left unitor for the structural semantic 1-cell associated to an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_leftUnitor_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K p))
      (reductionSeq_in_Theory1 K p) :=
  Theory2.leftUnitor K (reductionSeq_in_Theory1 K p)

/-- Composing the structural semantic comparison for `refl M · p` with the
endpoint equality of `concat_refl_left` yields the normalized semantic left
unitor, up to a semantic 3-cell.

This is the left-handed analogue of `reductionSeq_comp_rightUnitor_in_Theory3`
and is the exact normalization step needed in the `p = refl` base case of the
associator endpoint bridge. -/
noncomputable def reductionSeq_comp_leftUnitor_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p)
        (Theory2.ofEq K
          (congrArg (fun r => reductionSeq_in_Theory1 K r)
            (ReductionSeq.concat_refl_left p))))
      (reductionSeq_leftUnitor_in_Theory2 K p) :=
  Theory3.transReflRight K (reductionSeq_leftUnitor_in_Theory2 K p)

/-- The structural semantic comparison for `refl M · p` is already the semantic
left unitor, since the endpoint equality of `concat_refl_left` is definitionally
trivial at the `Theory1` level. This packages the normalized comparison without
the auxiliary `Theory2.ofEq` tail. -/
noncomputable def reductionSeq_comp_leftUnitor_direct_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory3 K
      (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p)
      (reductionSeq_leftUnitor_in_Theory2 K p) := by
  have hEq :
      congrArg (fun r => reductionSeq_in_Theory1 K r)
        (ReductionSeq.concat_refl_left p) = rfl := by
    exact Subsingleton.elim _ _
  exact Theory3.trans K
    (Theory3.symm K
      (Theory3.transReflRight K
        (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p)))
    (by
      cases hEq
      exact reductionSeq_comp_leftUnitor_in_Theory3 K p)

/-- Left unitor on a structural semantic composite is coherently the associator
followed by right whiskering of the left unitor. This is the normalized
left-handed counterpart of `reductionSeq_comp_rightUnitor_in_Theory3`. -/
noncomputable def reductionSeq_leftUnitorComp_in_Theory3
    (K : ExtensionalKanComplex) {M N P : Term}
    (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K
          (Theory1.refl K M)
          (reductionSeq_in_Theory1 K q)
          (reductionSeq_in_Theory1 K r))
        (Theory2.leftUnitor K
          (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))))
      (Theory2.whiskerRight K
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))
        (reductionSeq_in_Theory1 K r)) :=
  Theory3.leftUnitorComp K
    (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)

/-- Structural reduction-sequence wrapper for the left-unitor triangle
comparison
`triangle(associator(refl, q, r), whiskerRight(leftUnitor q, r)) ~ leftUnitor (q · r)`.

This packages the raw semantic triangle form of `reductionSeq_leftUnitorComp` so
the refl target-side bridge can work directly with triangle comparisons instead
of rebuilding the pointwise `Theory1` inputs. -/
noncomputable def reductionSeq_leftUnitorCompTriangleComparison_in_Theory3
    (K : ExtensionalKanComplex) {M N P : Term}
    (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (fun ρ =>
        let K0 := K.toReflexiveKanComplex.toKanComplex
        K0.trianglePath2
          (K0.associatorPath2
            (K0.reflPath (interpret K.toReflexiveKanComplex ρ M))
            (reductionSeq_in_Theory1 K q ρ)
            (reductionSeq_in_Theory1 K r ρ)).toTriangle
          (K0.whiskerRightPath2
            (K0.leftUnitorPath2 (reductionSeq_in_Theory1 K q ρ))
            (reductionSeq_in_Theory1 K r ρ)).toTriangle)
      (Theory2.leftUnitor K
        (Theory1.comp K
          (reductionSeq_in_Theory1 K q)
          (reductionSeq_in_Theory1 K r))) :=
  Theory3.leftUnitorCompTriangleComparison K
    (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)

/-- Left unitor naturality specialized to the structural semantic comparison
between an explicit composite and the interpretation of the concatenated path. -/
noncomputable def reductionSeq_leftUnitorNaturality_in_Theory3
    (K : ExtensionalKanComplex) {M N P : Term}
    (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K M)
          (reductionSeq_comp_in_Theory2 K q r))
        (Theory2.leftUnitor K
          (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))))
      (Theory2.trans K
        (Theory2.leftUnitor K
          (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)))
        (reductionSeq_comp_in_Theory2 K q r)) :=
  Theory3.leftUnitorNaturality K (reductionSeq_comp_in_Theory2 K q r)

/-- Right unitor for the structural semantic 1-cell associated to an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_rightUnitor_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (reductionSeq_in_Theory1 K p) (Theory1.refl K N))
      (reductionSeq_in_Theory1 K p) :=
  Theory2.rightUnitor K (reductionSeq_in_Theory1 K p)

/-- Structural-endpoint shell for the normalized semantic right unitor. This is
the comparison shape needed to relate the interpreted syntactic right unitor to
the normalized semantic right-unitor witness while staying on
`reductionSeq_in_Theory1` endpoints. -/
noncomputable def reductionSeq_rightUnitor_shell_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (reductionSeq_in_Theory1 K (ReductionSeq.concat p (ReductionSeq.refl N)))
      (reductionSeq_in_Theory1 K p) :=
  Theory2.trans K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K p (ReductionSeq.refl N)))
    (reductionSeq_rightUnitor_in_Theory2 K p)

/-- Composing the structural semantic comparison for `p · refl` with the
endpoint equality of `concat_refl_right` yields the normalized semantic right
unitor, up to a semantic 3-cell. -/
noncomputable def reductionSeq_comp_rightUnitor_in_Theory3
    (K : ExtensionalKanComplex) :
    {M N : Term} → (p : ReductionSeq M N) →
      Theory3 K
        (Theory2.trans K
          (reductionSeq_comp_in_Theory2 K p (ReductionSeq.refl N))
          (Theory2.ofEq K
            (congrArg (fun r => reductionSeq_in_Theory1 K r)
              (ReductionSeq.concat_refl_right p))))
        (reductionSeq_rightUnitor_in_Theory2 K p)
  | _, _, .refl M =>
      Theory3.trans K
        (Theory3.transReflRight K
          (reductionSeq_leftUnitor_in_Theory2 K (ReductionSeq.refl M)))
        (Theory3.reflUnitors K (M := M))
  | _, _, .step s rest => by
      let α := betaEtaStep_in_Theory1 K _ _ s
      let hRest := congrArg (fun r => reductionSeq_in_Theory1 K r)
        (ReductionSeq.concat_refl_right rest)
      let eRest : Theory2 K
          (reductionSeq_in_Theory1 K (ReductionSeq.concat rest (ReductionSeq.refl _)))
          (reductionSeq_in_Theory1 K rest) :=
        Theory2.ofEq K hRest
      let eStep : Theory2 K
          (reductionSeq_in_Theory1 K
              (ReductionSeq.concat (ReductionSeq.step s rest) (ReductionSeq.refl _)))
          (reductionSeq_in_Theory1 K (ReductionSeq.step s rest)) :=
        Theory2.ofEq K (congrArg (fun δ => Theory1.comp K α δ) hRest)
      have hWhiskEq :
          Theory3 K (Theory2.whiskerLeft K α eRest) eStep :=
        Theory3.whiskerLeftOfEq K α hRest
      have hInner :
          Theory3 K
            (Theory2.trans K
              (Theory2.whiskerLeft K α
                (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)))
              eStep)
            (Theory2.whiskerLeft K α
              (reductionSeq_rightUnitor_in_Theory2 K rest)) := by
        exact Theory3.trans K
          (Theory3.transCongrRight K
            (Theory2.whiskerLeft K α
              (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)))
            (Theory3.symm K hWhiskEq))
          (Theory3.trans K
            (Theory3.symm K (Theory3.whiskerLeftTrans K α
              (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)) eRest))
            (Theory3.whiskerLeftCongr K α
              (reductionSeq_comp_rightUnitor_in_Theory3 K rest)))
      exact Theory3.trans K
        (Theory3.transAssoc K
          (Theory2.associator K α (reductionSeq_in_Theory1 K rest) (Theory1.refl K _))
          (Theory2.whiskerLeft K α
            (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)))
          eStep)
        (Theory3.trans K
          (Theory3.transCongrRight K
            (Theory2.associator K α (reductionSeq_in_Theory1 K rest) (Theory1.refl K _))
            hInner)
          (Theory3.rightUnitorComp K α (reductionSeq_in_Theory1 K rest)))
  | _, _, .stepInv s rest => by
      let α := betaEtaStepInv_in_Theory1 K _ _ s
      let hRest := congrArg (fun r => reductionSeq_in_Theory1 K r)
        (ReductionSeq.concat_refl_right rest)
      let eRest : Theory2 K
          (reductionSeq_in_Theory1 K (ReductionSeq.concat rest (ReductionSeq.refl _)))
          (reductionSeq_in_Theory1 K rest) :=
        Theory2.ofEq K hRest
      let eStep : Theory2 K
          (reductionSeq_in_Theory1 K
              (ReductionSeq.concat (ReductionSeq.stepInv s rest) (ReductionSeq.refl _)))
          (reductionSeq_in_Theory1 K (ReductionSeq.stepInv s rest)) :=
        Theory2.ofEq K (congrArg (fun δ => Theory1.comp K α δ) hRest)
      have hWhiskEq :
          Theory3 K (Theory2.whiskerLeft K α eRest) eStep :=
        Theory3.whiskerLeftOfEq K α hRest
      have hInner :
          Theory3 K
            (Theory2.trans K
              (Theory2.whiskerLeft K α
                (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)))
              eStep)
            (Theory2.whiskerLeft K α
              (reductionSeq_rightUnitor_in_Theory2 K rest)) := by
        exact Theory3.trans K
          (Theory3.transCongrRight K
            (Theory2.whiskerLeft K α
              (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)))
            (Theory3.symm K hWhiskEq))
          (Theory3.trans K
            (Theory3.symm K (Theory3.whiskerLeftTrans K α
              (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)) eRest))
            (Theory3.whiskerLeftCongr K α
              (reductionSeq_comp_rightUnitor_in_Theory3 K rest)))
      exact Theory3.trans K
        (Theory3.transAssoc K
          (Theory2.associator K α (reductionSeq_in_Theory1 K rest) (Theory1.refl K _))
          (Theory2.whiskerLeft K α
            (reductionSeq_comp_in_Theory2 K rest (ReductionSeq.refl _)))
          eStep)
        (Theory3.trans K
          (Theory3.transCongrRight K
            (Theory2.associator K α (reductionSeq_in_Theory1 K rest) (Theory1.refl K _))
            hInner)
          (Theory3.rightUnitorComp K α (reductionSeq_in_Theory1 K rest)))

/-- The interpreted syntactic right unitor agrees with the structural-endpoint
right-unitor shell built from the normalized semantic right unitor. -/
noncomputable def homotopy2_rightUnitor_bridge_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (HigherTerms.rightUnitor p))
      (reductionSeq_rightUnitor_shell_in_Theory2 K p) := by
  let e : Theory2 K
      (reductionSeq_in_Theory1 K (ReductionSeq.concat p (ReductionSeq.refl N)))
      (reductionSeq_in_Theory1 K p) :=
    Theory2.ofEq K
      (congrArg (fun r => reductionSeq_in_Theory1 K r)
        (ReductionSeq.concat_refl_right p))
  have hShell : Theory3 K (reductionSeq_rightUnitor_shell_in_Theory2 K p) e := by
    let c := reductionSeq_comp_in_Theory2 K p (ReductionSeq.refl N)
    exact Theory3.trans K
      (Theory3.transCongrRight K (Theory2.symm K c)
        (Theory3.symm K (reductionSeq_comp_rightUnitor_in_Theory3 K p)))
      (Theory3.trans K
        (Theory3.symm K (Theory3.transAssoc K (Theory2.symm K c) c e))
        (Theory3.trans K
          (Theory3.transCongrLeft K (Theory3.transLeftCancel K c) e)
          (Theory3.transReflLeft K e)))
  have hInterp :
      homotopy2_in_Theory2 K (HigherTerms.rightUnitor p) = e :=
    homotopy2_in_Theory2_ofEq K (ReductionSeq.concat_refl_right p)
  exact hInterp ▸ Theory3.symm K hShell

/-- Structural-endpoint shell for the normalized semantic left unitor. This is
the comparison shape needed to relate the interpreted syntactic left unitor to
the normalized semantic left-unitor witness while staying on
`reductionSeq_in_Theory1` endpoints. -/
noncomputable def reductionSeq_leftUnitor_shell_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) p))
      (reductionSeq_in_Theory1 K p) :=
  Theory2.trans K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p))
    (reductionSeq_leftUnitor_in_Theory2 K p)

/-- Composing the explicit semantic comparison `comp_in refl p` with the structural
left-unitor shell recovers the normalized semantic left unitor. This packages the
endpoint bookkeeping needed to replace a raw `comp_in` leg by the left-unitor
shell in refl-specialized target-side calculations. -/
noncomputable def reductionSeq_comp_leftUnitor_shell_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p)
        (reductionSeq_leftUnitor_shell_in_Theory2 K p))
      (reductionSeq_leftUnitor_in_Theory2 K p) := by
  exact Theory3.trans K
    (Theory3.symm K
      (Theory3.transAssoc K
        (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p)
        (Theory2.symm K (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p))
        (reductionSeq_leftUnitor_in_Theory2 K p)))
    (Theory3.trans K
      (Theory3.transCongrLeft K
        (Theory3.transRightCancel K
          (reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) p))
        (reductionSeq_leftUnitor_in_Theory2 K p))
      (Theory3.transReflLeft K (reductionSeq_leftUnitor_in_Theory2 K p)))

/-- Appending the structural left-unitor shell to the raw refl target leg
normalizes the entire inner left-unitor composite route to the semantic
right-whiskered left unitor followed by the comparison `q · r -> q ++ r`.

This isolates the exact endpoint bookkeeping needed on the target side of the
refl associator bridge: the remaining difficulty is no longer the explicit
left-unitor shell itself, but only how that normalized factor interacts with the
outer whisker by an arbitrary `α`. -/
noncomputable def reductionSeq_leftUnitorCompShell_in_Theory3
    (K : ExtensionalKanComplex) {M N P : Term}
    (q : ReductionSeq M N) (r : ReductionSeq N P) :
    let δ := reductionSeq_in_Theory1 K r
    let c₀ := reductionSeq_comp_in_Theory2 K q r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
      (Theory2.trans K
        (Theory2.whiskerRight K
          (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ)
        c₀) := by
  let δ := reductionSeq_in_Theory1 K r
  let c₀ := reductionSeq_comp_in_Theory2 K q r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  have hShell :
      Theory3 K
        (Theory2.trans K e
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))
        (reductionSeq_leftUnitor_in_Theory2 K (ReductionSeq.concat q r)) := by
    simpa [e] using
      (reductionSeq_comp_leftUnitor_shell_in_Theory3 K (ReductionSeq.concat q r))
  have hTail :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r))))
        (Theory2.trans K
          (Theory2.leftUnitor K
            (Theory1.comp K (reductionSeq_in_Theory1 K q) δ))
          c₀) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K
        (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
        hShell)
      (reductionSeq_leftUnitorNaturality_in_Theory3 K q r)
  have hComp :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
          (Theory2.leftUnitor K
            (Theory1.comp K (reductionSeq_in_Theory1 K q) δ)))
        (Theory2.whiskerRight K
          (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ) :=
    reductionSeq_leftUnitorComp_in_Theory3 K q r
  exact Theory3.trans K
    (Theory3.transCongrRight K
      (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
      hTail)
    (Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K
          (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
          (Theory2.leftUnitor K
            (Theory1.comp K (reductionSeq_in_Theory1 K q) δ))
          c₀))
      (Theory3.transCongrLeft K hComp c₀))

/-- Structural-endpoint shell for the normalized semantic associator. The outer
endpoints stay on `reductionSeq_in_Theory1`, while the middle of the shell
passes through the semantic right-whiskered comparison, the semantic
associator, and the semantic left whisker of the target-side composition
comparison. -/
noncomputable def reductionSeq_associator_source_in_Theory2
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory2 K
      (reductionSeq_in_Theory1 K
        (ReductionSeq.concat (ReductionSeq.concat p q) r))
      (Theory1.comp K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
        (reductionSeq_in_Theory1 K r)) :=
  Theory2.trans K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K (ReductionSeq.concat p q) r))
    (Theory2.whiskerRight K
      (Theory2.symm K (reductionSeq_comp_in_Theory2 K p q))
      (reductionSeq_in_Theory1 K r))

/-- Target-side normalization leg for the structural associator shell. -/
noncomputable def reductionSeq_associator_target_in_Theory2
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory2 K
      (Theory1.comp K
        (reductionSeq_in_Theory1 K p)
        (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)))
      (reductionSeq_in_Theory1 K
        (ReductionSeq.concat p (ReductionSeq.concat q r))) :=
  Theory2.trans K
    (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p)
      (reductionSeq_comp_in_Theory2 K q r))
    (reductionSeq_comp_in_Theory2 K p (ReductionSeq.concat q r))

/-- Structural-endpoint shell for the normalized semantic associator. The outer
endpoints stay on `reductionSeq_in_Theory1`, while the middle of the shell
passes through the semantic right-whiskered comparison, the semantic
associator, and the semantic left whisker of the target-side composition
comparison. -/
noncomputable def reductionSeq_associator_shell_in_Theory2
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory2 K
      (reductionSeq_in_Theory1 K
        (ReductionSeq.concat (ReductionSeq.concat p q) r))
      (reductionSeq_in_Theory1 K
        (ReductionSeq.concat p (ReductionSeq.concat q r))) :=
  Theory2.trans K
    (reductionSeq_associator_source_in_Theory2 K p q r)
    (Theory2.trans K
      (reductionSeq_associator_in_Theory2 K p q r)
      (reductionSeq_associator_target_in_Theory2 K p q r))

/-- Source-side normalization for the structural associator shell when the left
explicit path begins with a forward βη step, assuming the special
left-whisker/right-whisker comparison for the composition shell on the tail.

This isolates the purely algebraic part of the source-side head bridge: once the
`whiskerLeftWhiskerRight`-style comparison for `reductionSeq_comp_in_Theory2`
is available, the remaining shell normalization is generic. -/
noncomputable def reductionSeq_associator_source_step_from_wlwr_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hWLWR :
      Theory3 K
        (Theory2.whiskerRight K
          (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K L M s)
            (reductionSeq_comp_in_Theory2 K rest q))
          (reductionSeq_in_Theory1 K r))
        (Theory2.trans K
          (Theory2.associator K
            (betaEtaStep_in_Theory1 K L M s)
            (Theory1.comp K
              (reductionSeq_in_Theory1 K rest)
              (reductionSeq_in_Theory1 K q))
            (reductionSeq_in_Theory1 K r))
          (Theory2.trans K
            (Theory2.whiskerLeft K
              (betaEtaStep_in_Theory1 K L M s)
              (Theory2.whiskerRight K
                (reductionSeq_comp_in_Theory2 K rest q)
                (reductionSeq_in_Theory1 K r)))
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStep_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q))
                (reductionSeq_in_Theory1 K r)))))) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStep_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStep_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  let β := reductionSeq_in_Theory1 K rest
  let γ := reductionSeq_in_Theory1 K q
  let δ := reductionSeq_in_Theory1 K r
  let βγs := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
  let c1 := reductionSeq_comp_in_Theory2 K rest q
  let c2 := reductionSeq_comp_in_Theory2 K (ReductionSeq.concat rest q) r
  let c1s := reductionSeq_comp_in_Theory2 K (ReductionSeq.step s rest) q
  let c2s := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.step s rest) q) r
  let A1 := Theory2.associator K α β γ
  let A2 := Theory2.associator K α βγs δ
  let A2c := Theory2.associator K α (Theory1.comp K β γ) δ
  let sourceRest := reductionSeq_associator_source_in_Theory2 K rest q r
  let wrsc1 := Theory2.whiskerRight K (Theory2.symm K c1) δ
  let αwrsc1 := Theory2.whiskerLeft K α wrsc1
  let wrsA1 := Theory2.whiskerRight K (Theory2.symm K A1) δ
  have hSymmC2s :
      Theory3 K
        (Theory2.symm K c2s)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          (Theory2.symm K A2)) := by
    exact Theory3.trans K
      (by
        simpa [c2s, A2, c2, α, βγs, δ, reductionSeq_comp_in_Theory2,
          ReductionSeq.concat, reductionSeq_in_Theory1] using
          (Theory3.symmTrans K A2 (Theory2.whiskerLeft K α c2)))
      (Theory3.transCongrLeft K
        (Theory3.invWhiskerLeft K α c2)
        (Theory2.symm K A2))
  have hWLWR' :
      Theory3 K
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)
        (Theory2.trans K A2c
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
            (Theory2.symm K A2))) := by
    simpa [A2c, A2, α, β, γ, δ, c1, reductionSeq_in_Theory1] using hWLWR
  have hWrsC1_left :
      Theory3 K
        (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
        (Theory2.trans K A2
          (Theory2.trans K αwrsc1 (Theory2.symm K A2c))) := by
    have hSymm0 :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
          (Theory2.symm K
            (Theory2.trans K A2c
              (Theory2.trans K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
                (Theory2.symm K A2)))) :=
      Theory3.symmCongr K hWLWR'
    have hSymm1 :
        Theory3 K
          (Theory2.symm K
            (Theory2.trans K A2c
              (Theory2.trans K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
                (Theory2.symm K A2))))
          (Theory2.trans K
            (Theory2.symm K
              (Theory2.trans K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
                (Theory2.symm K A2)))
            (Theory2.symm K A2c)) :=
      Theory3.symmTrans K A2c
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
          (Theory2.symm K A2))
    have hSymm2 :
        Theory3 K
          (Theory2.symm K
            (Theory2.trans K
              (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
              (Theory2.symm K A2)))
          (Theory2.trans K
            (Theory2.symm K (Theory2.symm K A2))
            (Theory2.symm K
              (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))) :=
      Theory3.symmTrans K
        (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
        (Theory2.symm K A2)
    have hA2ss :
        Theory3 K
          (Theory2.symm K (Theory2.symm K A2))
          A2 :=
      Theory3.symmSymm K A2
    have hLeftSymm :
        Theory3 K
          (Theory2.symm K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
          (Theory2.whiskerLeft K α
            (Theory2.symm K (Theory2.whiskerRight K c1 δ))) :=
      Theory3.invWhiskerLeft K α (Theory2.whiskerRight K c1 δ)
    have hRightSymm :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K c1 δ))
          wrsc1 :=
      Theory3.invWhiskerRight K c1 δ
    have hInner :
        Theory3 K
          (Theory2.trans K
            (Theory2.symm K
              (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
            (Theory2.symm K A2c))
          (Theory2.trans K αwrsc1 (Theory2.symm K A2c)) := by
      exact Theory3.trans K
        (Theory3.transCongrLeft K hLeftSymm (Theory2.symm K A2c))
        (Theory3.transCongrLeft K
          (Theory3.whiskerLeftCongr K α hRightSymm)
          (Theory2.symm K A2c))
    exact Theory3.trans K hSymm0
      (Theory3.trans K hSymm1
        (Theory3.trans K
          (Theory3.transCongrLeft K hSymm2 (Theory2.symm K A2c))
          (Theory3.trans K
            (Theory3.transAssoc K
              (Theory2.symm K (Theory2.symm K A2))
              (Theory2.symm K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
              (Theory2.symm K A2c))
            (Theory3.trans K
              (Theory3.transCongrLeft K hA2ss
                (Theory2.trans K
                  (Theory2.symm K
                    (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
                  (Theory2.symm K A2c)))
              (Theory3.transCongrRight K A2 hInner)))))
  have hWrsC1 :
      Theory3 K
        (Theory2.whiskerRight K (Theory2.symm K c1s) δ)
        (Theory2.trans K A2
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))) := by
    have h0 :
        Theory3 K
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ)
          (Theory2.symm K (Theory2.whiskerRight K c1s δ)) :=
      Theory3.whiskerRightSymm K c1s δ
    have h1 :
        Theory3 K
          (Theory2.whiskerRight K c1s δ)
          (Theory2.trans K
            (Theory2.whiskerRight K A1 δ)
            (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)) := by
      simpa [c1s, A1, c1, α, β, γ, reductionSeq_comp_in_Theory2,
        reductionSeq_in_Theory1] using
        (Theory3.whiskerRightTrans K A1 (Theory2.whiskerLeft K α c1) δ)
    have h2 :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K c1s δ))
          (Theory2.symm K
            (Theory2.trans K
              (Theory2.whiskerRight K A1 δ)
              (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))) :=
      Theory3.symmCongr K h1
    have h3 :
        Theory3 K
          (Theory2.symm K
            (Theory2.trans K
              (Theory2.whiskerRight K A1 δ)
              (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)))
          (Theory2.trans K
            (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ))) :=
      Theory3.symmTrans K
        (Theory2.whiskerRight K A1 δ)
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)
    have h4 :
        Theory3 K
          (Theory2.trans K
            (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ)))
          (Theory2.trans K
            (Theory2.trans K A2
              (Theory2.trans K αwrsc1 (Theory2.symm K A2c)))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ))) :=
      Theory3.transCongrLeft K hWrsC1_left
        (Theory2.symm K (Theory2.whiskerRight K A1 δ))
    have h5 :
        Theory3 K
          (Theory2.trans K
            (Theory2.trans K A2
              (Theory2.trans K αwrsc1 (Theory2.symm K A2c)))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ)))
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c)
                (Theory2.symm K (Theory2.whiskerRight K A1 δ))))) := by
      exact Theory3.trans K
        (Theory3.transAssoc K A2
          (Theory2.trans K αwrsc1 (Theory2.symm K A2c))
          (Theory2.symm K (Theory2.whiskerRight K A1 δ)))
        (Theory3.transCongrRight K A2
          (Theory3.transAssoc K αwrsc1 (Theory2.symm K A2c)
            (Theory2.symm K (Theory2.whiskerRight K A1 δ))))
    have h6 :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K A1 δ))
          wrsA1 :=
      Theory3.invWhiskerRight K A1 δ
    exact Theory3.trans K h0
      (Theory3.trans K h2
        (Theory3.trans K h3
          (Theory3.trans K h4
            (Theory3.trans K h5
              (Theory3.transCongrRight K A2
                (Theory3.transCongrRight K αwrsc1
                  (Theory3.transCongrRight K (Theory2.symm K A2c) h6)))))))
  have hS0 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K c2s)
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ)) :=
    Theory3.transCongrLeft K hSymmC2s
      (Theory2.whiskerRight K (Theory2.symm K c1s) δ)
  have hS1 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c) wrsA1)))) :=
    Theory3.transCongrRight K
      (Theory2.trans K
        (Theory2.whiskerLeft K α (Theory2.symm K c2))
        (Theory2.symm K A2))
      hWrsC1
  have hCancelA2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K A2)
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
        (Theory2.trans K αwrsc1
          (Theory2.trans K (Theory2.symm K A2c) wrsA1)) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K A2) A2
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
      (Theory3.trans K
        (Theory3.transCongrLeft K (Theory3.transLeftCancel K A2)
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1)))
        (Theory3.transReflLeft K
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
  have hS2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))) := by
    exact Theory3.trans K
      (Theory3.transAssoc K
        (Theory2.whiskerLeft K α (Theory2.symm K c2))
        (Theory2.symm K A2)
        (Theory2.trans K A2
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
      (Theory3.transCongrRight K
        (Theory2.whiskerLeft K α (Theory2.symm K c2))
        hCancelA2)
  have hCombineSrc :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          αwrsc1)
        (Theory2.whiskerLeft K α sourceRest) := by
    simpa [sourceRest, reductionSeq_associator_source_in_Theory2, wrsc1, c2, c1]
      using
        (Theory3.symm K
          (Theory3.whiskerLeftTrans K α (Theory2.symm K c2) wrsc1))
  have hS3 :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1)))
        (Theory2.trans K
          (Theory2.whiskerLeft K α sourceRest)
          (Theory2.trans K (Theory2.symm K A2c) wrsA1)) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          αwrsc1
          (Theory2.trans K (Theory2.symm K A2c) wrsA1)))
      (Theory3.transCongrLeft K hCombineSrc
        (Theory2.trans K (Theory2.symm K A2c) wrsA1))
  simpa [reductionSeq_associator_source_in_Theory2, c1s, c2s, sourceRest, wrsc1,
    αwrsc1, wrsA1, A1, A2, A2c, α, β, γ, δ, βγs, c1, c2,
    reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1, ReductionSeq.concat]
    using
      (Theory3.trans K hS0
        (Theory3.trans K hS1 (Theory3.trans K hS2 hS3)))

/-- Once the WLWR midpoint/right comparison is identified with the direct
pentagon whisker-front path for the tail composition shell, the forward
source-step head bridge follows immediately. -/
noncomputable def reductionSeq_associator_source_step_from_pentagonWhiskerFront_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hMidFront :
      let α := betaEtaStep_in_Theory1 K L M s
      let η := reductionSeq_comp_in_Theory2 K rest q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ))) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStep_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStep_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  have hWLWR :
      Theory3 K
        (Theory2.whiskerRight K
          (Theory2.whiskerLeft K α η)
          δ)
        (Theory2.trans K
          (Theory2.associator K
            α
            (Theory1.comp K
              (reductionSeq_in_Theory1 K rest)
              (reductionSeq_in_Theory1 K q))
            δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K
              (Theory2.associator K
                α
                (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q))
                δ)))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightFromTriangleComparison K α η δ
        (Theory3.whiskerLeftWhiskerRightFromPentagonWhiskerFrontComparison
          K α η δ hMidFront))
  exact reductionSeq_associator_source_step_from_wlwr_in_Theory3 K s rest q r hWLWR

/-- Forward-step reduced triangle witness for the tail composition shell, assuming
the midpoint/front comparison against the direct pentagon whisker-front path. -/
noncomputable def reductionSeq_comp_triangle_target_step_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hMidFront :
      let α := betaEtaStep_in_Theory1 K L M s
      let η := reductionSeq_comp_in_Theory2 K rest q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ))) :
    let α := betaEtaStep_in_Theory1 K L M s
    let β := Theory1.comp K
      (reductionSeq_in_Theory1 K rest)
      (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
    let η := reductionSeq_comp_in_Theory2 K rest q
    let δ := reductionSeq_in_Theory1 K r
    Theory3 K
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toReflexiveKanComplex.toKanComplex.associatorPath2
            (α ρ) (β ρ) (δ ρ)).toTriangle
          (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ) (η ρ))
            (δ ρ)).toTriangle)
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.transPath2
          (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
            (α ρ)
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (η ρ) (δ ρ)))
          (K.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ)))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  simpa [α, η, δ] using
    (Theory3.whiskerLeftWhiskerRightFromPentagonWhiskerFrontComparison K α η δ
      hMidFront)

/-- Once the specialized reduced triangle comparison is available for the tail
composition shell, the forward source-step head bridge follows immediately. -/
noncomputable def reductionSeq_associator_source_step_from_triangle_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hTri :
      let α := betaEtaStep_in_Theory1 K L M s
      let β := Theory1.comp K
        (reductionSeq_in_Theory1 K rest)
        (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let η := reductionSeq_comp_in_Theory2 K rest q
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) ) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStep_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStep_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  have hWLWR :
      Theory3 K
        (Theory2.whiskerRight K
          (Theory2.whiskerLeft K α η)
          δ)
        (Theory2.trans K
          (Theory2.associator K
            α
            (Theory1.comp K
              (reductionSeq_in_Theory1 K rest)
              (reductionSeq_in_Theory1 K q))
            δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K
              (Theory2.associator K
                α
                (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q))
                δ)))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightFromTriangleComparison K α η δ hTri)
  simpa [α, η, δ] using
    reductionSeq_associator_source_step_from_wlwr_in_Theory3 K s rest q r hWLWR

/-- Once the reduced WLWR right-half comparison is available for the tail
composition shell, the forward source-step head bridge follows immediately. -/
noncomputable def reductionSeq_associator_source_step_from_rightComparison_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hRight :
      let α := betaEtaStep_in_Theory1 K L M s
      let η := reductionSeq_comp_in_Theory2 K rest q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ)))) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStep_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStep_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  have hMidFront :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ)
            (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q) ρ)
            (δ ρ)) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonFromTriangleComparison
        K α η δ hRight)
  have hTri :
      let β := Theory1.comp K
        (reductionSeq_in_Theory1 K rest)
        (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightFromPentagonWhiskerFrontComparison
        K α η δ hMidFront)
  simpa [α, η, δ] using
    reductionSeq_associator_source_step_from_triangle_in_Theory3 K s rest q r hTri

/-- Inverse-step analogue of
`reductionSeq_associator_source_step_from_wlwr_in_Theory3`.

As in the forward case, all source-side bookkeeping is generic once the
special `whiskerLeftWhiskerRight` comparison for the tail composition shell is
available. -/
noncomputable def reductionSeq_associator_source_stepInv_from_wlwr_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hWLWR :
      Theory3 K
        (Theory2.whiskerRight K
          (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K L M s)
            (reductionSeq_comp_in_Theory2 K rest q))
          (reductionSeq_in_Theory1 K r))
        (Theory2.trans K
          (Theory2.associator K
            (betaEtaStepInv_in_Theory1 K L M s)
            (Theory1.comp K
              (reductionSeq_in_Theory1 K rest)
              (reductionSeq_in_Theory1 K q))
            (reductionSeq_in_Theory1 K r))
          (Theory2.trans K
            (Theory2.whiskerLeft K
              (betaEtaStepInv_in_Theory1 K L M s)
              (Theory2.whiskerRight K
                (reductionSeq_comp_in_Theory2 K rest q)
                (reductionSeq_in_Theory1 K r)))
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStepInv_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q))
                (reductionSeq_in_Theory1 K r)))))) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStepInv_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStepInv_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let β := reductionSeq_in_Theory1 K rest
  let γ := reductionSeq_in_Theory1 K q
  let δ := reductionSeq_in_Theory1 K r
  let βγs := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
  let c1 := reductionSeq_comp_in_Theory2 K rest q
  let c2 := reductionSeq_comp_in_Theory2 K (ReductionSeq.concat rest q) r
  let c1s := reductionSeq_comp_in_Theory2 K (ReductionSeq.stepInv s rest) q
  let c2s := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.stepInv s rest) q) r
  let A1 := Theory2.associator K α β γ
  let A2 := Theory2.associator K α βγs δ
  let A2c := Theory2.associator K α (Theory1.comp K β γ) δ
  let sourceRest := reductionSeq_associator_source_in_Theory2 K rest q r
  let wrsc1 := Theory2.whiskerRight K (Theory2.symm K c1) δ
  let αwrsc1 := Theory2.whiskerLeft K α wrsc1
  let wrsA1 := Theory2.whiskerRight K (Theory2.symm K A1) δ
  have hSymmC2s :
      Theory3 K
        (Theory2.symm K c2s)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          (Theory2.symm K A2)) := by
    exact Theory3.trans K
      (by
        simpa [c2s, A2, c2, α, βγs, δ, reductionSeq_comp_in_Theory2,
          ReductionSeq.concat, reductionSeq_in_Theory1] using
          (Theory3.symmTrans K A2 (Theory2.whiskerLeft K α c2)))
      (Theory3.transCongrLeft K
        (Theory3.invWhiskerLeft K α c2)
        (Theory2.symm K A2))
  have hWLWR' :
      Theory3 K
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)
        (Theory2.trans K A2c
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
            (Theory2.symm K A2))) := by
    simpa [A2c, A2, α, β, γ, δ, c1, reductionSeq_in_Theory1] using hWLWR
  have hWrsC1_left :
      Theory3 K
        (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
        (Theory2.trans K A2
          (Theory2.trans K αwrsc1 (Theory2.symm K A2c))) := by
    have hSymm0 :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
          (Theory2.symm K
            (Theory2.trans K A2c
              (Theory2.trans K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
                (Theory2.symm K A2)))) :=
      Theory3.symmCongr K hWLWR'
    have hSymm1 :
        Theory3 K
          (Theory2.symm K
            (Theory2.trans K A2c
              (Theory2.trans K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
                (Theory2.symm K A2))))
          (Theory2.trans K
            (Theory2.symm K
              (Theory2.trans K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
                (Theory2.symm K A2)))
            (Theory2.symm K A2c)) :=
      Theory3.symmTrans K A2c
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
          (Theory2.symm K A2))
    have hSymm2 :
        Theory3 K
          (Theory2.symm K
            (Theory2.trans K
              (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
              (Theory2.symm K A2)))
          (Theory2.trans K
            (Theory2.symm K (Theory2.symm K A2))
            (Theory2.symm K
              (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))) :=
      Theory3.symmTrans K
        (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ))
        (Theory2.symm K A2)
    have hA2ss :
        Theory3 K
          (Theory2.symm K (Theory2.symm K A2))
          A2 :=
      Theory3.symmSymm K A2
    have hLeftSymm :
        Theory3 K
          (Theory2.symm K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
          (Theory2.whiskerLeft K α
            (Theory2.symm K (Theory2.whiskerRight K c1 δ))) :=
      Theory3.invWhiskerLeft K α (Theory2.whiskerRight K c1 δ)
    have hRightSymm :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K c1 δ))
          wrsc1 :=
      Theory3.invWhiskerRight K c1 δ
    have hInner :
        Theory3 K
          (Theory2.trans K
            (Theory2.symm K
              (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
            (Theory2.symm K A2c))
          (Theory2.trans K αwrsc1 (Theory2.symm K A2c)) := by
      exact Theory3.trans K
        (Theory3.transCongrLeft K hLeftSymm (Theory2.symm K A2c))
        (Theory3.transCongrLeft K
          (Theory3.whiskerLeftCongr K α hRightSymm)
          (Theory2.symm K A2c))
    exact Theory3.trans K hSymm0
      (Theory3.trans K hSymm1
        (Theory3.trans K
          (Theory3.transCongrLeft K hSymm2 (Theory2.symm K A2c))
          (Theory3.trans K
            (Theory3.transAssoc K
              (Theory2.symm K (Theory2.symm K A2))
              (Theory2.symm K
                (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
              (Theory2.symm K A2c))
            (Theory3.trans K
              (Theory3.transCongrLeft K hA2ss
                (Theory2.trans K
                  (Theory2.symm K
                    (Theory2.whiskerLeft K α (Theory2.whiskerRight K c1 δ)))
                  (Theory2.symm K A2c)))
              (Theory3.transCongrRight K A2 hInner)))))
  have hWrsC1 :
      Theory3 K
        (Theory2.whiskerRight K (Theory2.symm K c1s) δ)
        (Theory2.trans K A2
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))) := by
    have h0 :
        Theory3 K
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ)
          (Theory2.symm K (Theory2.whiskerRight K c1s δ)) :=
      Theory3.whiskerRightSymm K c1s δ
    have h1 :
        Theory3 K
          (Theory2.whiskerRight K c1s δ)
          (Theory2.trans K
            (Theory2.whiskerRight K A1 δ)
            (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)) := by
      simpa [c1s, A1, c1, α, β, γ, reductionSeq_comp_in_Theory2,
        reductionSeq_in_Theory1] using
        (Theory3.whiskerRightTrans K A1 (Theory2.whiskerLeft K α c1) δ)
    have h2 :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K c1s δ))
          (Theory2.symm K
            (Theory2.trans K
              (Theory2.whiskerRight K A1 δ)
              (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))) :=
      Theory3.symmCongr K h1
    have h3 :
        Theory3 K
          (Theory2.symm K
            (Theory2.trans K
              (Theory2.whiskerRight K A1 δ)
              (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)))
          (Theory2.trans K
            (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ))) :=
      Theory3.symmTrans K
        (Theory2.whiskerRight K A1 δ)
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ)
    have h4 :
        Theory3 K
          (Theory2.trans K
            (Theory2.symm K (Theory2.whiskerRight K (Theory2.whiskerLeft K α c1) δ))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ)))
          (Theory2.trans K
            (Theory2.trans K A2
              (Theory2.trans K αwrsc1 (Theory2.symm K A2c)))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ))) :=
      Theory3.transCongrLeft K hWrsC1_left
        (Theory2.symm K (Theory2.whiskerRight K A1 δ))
    have h5 :
        Theory3 K
          (Theory2.trans K
            (Theory2.trans K A2
              (Theory2.trans K αwrsc1 (Theory2.symm K A2c)))
            (Theory2.symm K (Theory2.whiskerRight K A1 δ)))
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c)
                (Theory2.symm K (Theory2.whiskerRight K A1 δ))))) := by
      exact Theory3.trans K
        (Theory3.transAssoc K A2
          (Theory2.trans K αwrsc1 (Theory2.symm K A2c))
          (Theory2.symm K (Theory2.whiskerRight K A1 δ)))
        (Theory3.transCongrRight K A2
          (Theory3.transAssoc K αwrsc1 (Theory2.symm K A2c)
            (Theory2.symm K (Theory2.whiskerRight K A1 δ))))
    have h6 :
        Theory3 K
          (Theory2.symm K (Theory2.whiskerRight K A1 δ))
          wrsA1 :=
      Theory3.invWhiskerRight K A1 δ
    exact Theory3.trans K h0
      (Theory3.trans K h2
        (Theory3.trans K h3
          (Theory3.trans K h4
            (Theory3.trans K h5
              (Theory3.transCongrRight K A2
                (Theory3.transCongrRight K αwrsc1
                  (Theory3.transCongrRight K (Theory2.symm K A2c) h6)))))))
  have hS0 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K c2s)
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ)) :=
    Theory3.transCongrLeft K hSymmC2s
      (Theory2.whiskerRight K (Theory2.symm K c1s) δ)
  have hS1 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.whiskerRight K (Theory2.symm K c1s) δ))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c) wrsA1)))) :=
    Theory3.transCongrRight K
      (Theory2.trans K
        (Theory2.whiskerLeft K α (Theory2.symm K c2))
        (Theory2.symm K A2))
      hWrsC1
  have hCancelA2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K A2)
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
        (Theory2.trans K αwrsc1
          (Theory2.trans K (Theory2.symm K A2c) wrsA1)) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K A2) A2
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
      (Theory3.trans K
        (Theory3.transCongrLeft K (Theory3.transLeftCancel K A2)
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1)))
        (Theory3.transReflLeft K
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
  have hS2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.symm K c2))
            (Theory2.symm K A2))
          (Theory2.trans K A2
            (Theory2.trans K αwrsc1
              (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))) := by
    exact Theory3.trans K
      (Theory3.transAssoc K
        (Theory2.whiskerLeft K α (Theory2.symm K c2))
        (Theory2.symm K A2)
        (Theory2.trans K A2
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1))))
      (Theory3.transCongrRight K
        (Theory2.whiskerLeft K α (Theory2.symm K c2))
        hCancelA2)
  have hCombineSrc :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          αwrsc1)
        (Theory2.whiskerLeft K α sourceRest) := by
    simpa [sourceRest, reductionSeq_associator_source_in_Theory2, wrsc1, c2, c1]
      using
        (Theory3.symm K
          (Theory3.whiskerLeftTrans K α (Theory2.symm K c2) wrsc1))
  have hS3 :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          (Theory2.trans K αwrsc1
            (Theory2.trans K (Theory2.symm K A2c) wrsA1)))
        (Theory2.trans K
          (Theory2.whiskerLeft K α sourceRest)
          (Theory2.trans K (Theory2.symm K A2c) wrsA1)) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K
          (Theory2.whiskerLeft K α (Theory2.symm K c2))
          αwrsc1
          (Theory2.trans K (Theory2.symm K A2c) wrsA1)))
      (Theory3.transCongrLeft K hCombineSrc
        (Theory2.trans K (Theory2.symm K A2c) wrsA1))
  simpa [reductionSeq_associator_source_in_Theory2, c1s, c2s, sourceRest, wrsc1,
    αwrsc1, wrsA1, A1, A2, A2c, α, β, γ, δ, βγs, c1, c2,
    reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1, ReductionSeq.concat]
    using
      (Theory3.trans K hS0
        (Theory3.trans K hS1 (Theory3.trans K hS2 hS3)))

/-- Inverse-step analogue of
`reductionSeq_associator_source_step_from_pentagonWhiskerFront_in_Theory3`. -/
noncomputable def reductionSeq_associator_source_stepInv_from_pentagonWhiskerFront_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hMidFront :
      let α := betaEtaStepInv_in_Theory1 K L M s
      let η := reductionSeq_comp_in_Theory2 K rest q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ))) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStepInv_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStepInv_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  have hWLWR :
      Theory3 K
        (Theory2.whiskerRight K
          (Theory2.whiskerLeft K α η)
          δ)
        (Theory2.trans K
          (Theory2.associator K
            α
            (Theory1.comp K
              (reductionSeq_in_Theory1 K rest)
              (reductionSeq_in_Theory1 K q))
            δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K
              (Theory2.associator K
                α
                (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q))
                δ)))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightFromTriangleComparison K α η δ
        (Theory3.whiskerLeftWhiskerRightFromPentagonWhiskerFrontComparison
          K α η δ hMidFront))
  exact reductionSeq_associator_source_stepInv_from_wlwr_in_Theory3 K s rest q r hWLWR

/-- Inverse-step reduced triangle witness for the tail composition shell,
assuming the midpoint/front comparison against the direct pentagon
whisker-front path. -/
noncomputable def reductionSeq_comp_triangle_target_stepInv_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hMidFront :
      let α := betaEtaStepInv_in_Theory1 K L M s
      let η := reductionSeq_comp_in_Theory2 K rest q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ))) :
    let α := betaEtaStepInv_in_Theory1 K L M s
    let β := Theory1.comp K
      (reductionSeq_in_Theory1 K rest)
      (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
    let η := reductionSeq_comp_in_Theory2 K rest q
    let δ := reductionSeq_in_Theory1 K r
    Theory3 K
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toReflexiveKanComplex.toKanComplex.associatorPath2
            (α ρ) (β ρ) (δ ρ)).toTriangle
          (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ) (η ρ))
            (δ ρ)).toTriangle)
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.transPath2
          (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
            (α ρ)
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (η ρ) (δ ρ)))
          (K.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ)))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  simpa [α, η, δ] using
    (Theory3.whiskerLeftWhiskerRightFromPentagonWhiskerFrontComparison K α η δ
      hMidFront)

/-- Inverse-step analogue of
`reductionSeq_associator_source_step_from_triangle_in_Theory3`. -/
noncomputable def reductionSeq_associator_source_stepInv_from_triangle_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hTri :
      let α := betaEtaStepInv_in_Theory1 K L M s
      let β := Theory1.comp K
        (reductionSeq_in_Theory1 K rest)
        (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let η := reductionSeq_comp_in_Theory2 K rest q
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) ) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStepInv_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStepInv_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  have hWLWR :
      Theory3 K
        (Theory2.whiskerRight K
          (Theory2.whiskerLeft K α η)
          δ)
        (Theory2.trans K
          (Theory2.associator K
            α
            (Theory1.comp K
              (reductionSeq_in_Theory1 K rest)
              (reductionSeq_in_Theory1 K q))
            δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K
              (Theory2.associator K
                α
                (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q))
                δ)))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightFromTriangleComparison K α η δ hTri)
  simpa [α, η, δ] using
    reductionSeq_associator_source_stepInv_from_wlwr_in_Theory3 K s rest q r hWLWR

/-- Once the reduced WLWR right-half comparison is available for the tail
composition shell, the inverse source-step head bridge follows immediately. -/
noncomputable def reductionSeq_associator_source_stepInv_from_rightComparison_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hRight :
      let α := betaEtaStepInv_in_Theory1 K L M s
      let η := reductionSeq_comp_in_Theory2 K rest q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ)))) :
    Theory3 K
      (reductionSeq_associator_source_in_Theory2 K
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K
        (Theory2.whiskerLeft K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_source_in_Theory2 K rest q r))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.associator K
              (betaEtaStepInv_in_Theory1 K L M s)
              (Theory1.comp K
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q))
              (reductionSeq_in_Theory1 K r)))
          (Theory2.whiskerRight K
            (Theory2.symm K
              (Theory2.associator K
                (betaEtaStepInv_in_Theory1 K L M s)
                (reductionSeq_in_Theory1 K rest)
                (reductionSeq_in_Theory1 K q)))
            (reductionSeq_in_Theory1 K r)))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let η := reductionSeq_comp_in_Theory2 K rest q
  let δ := reductionSeq_in_Theory1 K r
  have hMidFront :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ)
            (reductionSeq_in_Theory1 K (ReductionSeq.concat rest q) ρ)
            (δ ρ)) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonFromTriangleComparison
        K α η δ hRight)
  have hTri :
      let β := Theory1.comp K
        (reductionSeq_in_Theory1 K rest)
        (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat rest q)
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightFromPentagonWhiskerFrontComparison
        K α η δ hMidFront)
  simpa [α, η, δ] using
    reductionSeq_associator_source_stepInv_from_triangle_in_Theory3 K s rest q r hTri

/-- Target-side normalization for the structural associator shell when the left
explicit path begins with a forward βη step. This isolates the right half of
the step-head bridge: the stepped target leg already reduces to the semantic
associator followed by the left whisker of the tail target leg. -/
noncomputable def reductionSeq_associator_target_step_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K
      (reductionSeq_associator_target_in_Theory2 K
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K
        (Theory2.associator K
          (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_in_Theory1 K rest)
          (Theory1.comp K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)))
        (Theory2.whiskerLeft K
          (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_associator_target_in_Theory2 K rest q r))) := by
  let α := betaEtaStep_in_Theory1 K L M s
  let β := reductionSeq_in_Theory1 K rest
  let γ := reductionSeq_in_Theory1 K q
  let δ := reductionSeq_in_Theory1 K r
  let d := reductionSeq_comp_in_Theory2 K q r
  let e := reductionSeq_comp_in_Theory2 K rest (ReductionSeq.concat q r)
  let A3 := Theory2.associator K α β (Theory1.comp K γ δ)
  let A4 := Theory2.associator K α β (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))
  let W := Theory2.whiskerLeft K α (Theory2.whiskerLeft K β d)
  let αe := Theory2.whiskerLeft K α e
  let targetRest := reductionSeq_associator_target_in_Theory2 K rest q r
  let X := Theory2.whiskerLeft K (Theory1.comp K α β) d
  let eStep := reductionSeq_comp_in_Theory2 K (ReductionSeq.step s rest) (ReductionSeq.concat q r)
  have hWhisk :
      Theory3 K X
        (Theory2.trans K A3
          (Theory2.trans K W (Theory2.symm K A4))) := by
    simpa [X, A3, A4, W, α, β, γ, δ, d] using
      (Theory3.whiskerLeftComp K α β d)
  have hE :
      Theory3 K eStep
        (Theory2.trans K A4 αe) := by
    simpa [eStep, A4, α, β, e, αe, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
      reductionSeq_in_Theory1] using
      (Theory3.refl K eStep)
  have h0 :
      Theory3 K
        (Theory2.trans K X eStep)
        (Theory2.trans K X (Theory2.trans K A4 αe)) :=
    Theory3.transCongrRight K X hE
  have h1 :
      Theory3 K
        (Theory2.trans K X (Theory2.trans K A4 αe))
        (Theory2.trans K
          (Theory2.trans K A3 (Theory2.trans K W (Theory2.symm K A4)))
          (Theory2.trans K A4 αe)) :=
    Theory3.transCongrLeft K hWhisk (Theory2.trans K A4 αe)
  have hCancelA4 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K A4) (Theory2.trans K A4 αe))
        αe := by
    exact Theory3.trans K
      (Theory3.symm K (Theory3.transAssoc K (Theory2.symm K A4) A4 αe))
      (Theory3.trans K
        (Theory3.transCongrLeft K (Theory3.transLeftCancel K A4) αe)
        (Theory3.transReflLeft K αe))
  have h2_inner :
      Theory3 K
        (Theory2.trans K (Theory2.trans K W (Theory2.symm K A4)) (Theory2.trans K A4 αe))
        (Theory2.trans K W αe) := by
    exact Theory3.trans K
      (Theory3.transAssoc K W (Theory2.symm K A4) (Theory2.trans K A4 αe))
      (Theory3.transCongrRight K W hCancelA4)
  have h2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K A3 (Theory2.trans K W (Theory2.symm K A4)))
          (Theory2.trans K A4 αe))
        (Theory2.trans K A3 (Theory2.trans K W αe)) := by
    exact Theory3.trans K
      (Theory3.transAssoc K A3 (Theory2.trans K W (Theory2.symm K A4)) (Theory2.trans K A4 αe))
      (Theory3.transCongrRight K A3 h2_inner)
  have hRestWhisk :
      Theory3 K
        (Theory2.trans K W αe)
        (Theory2.whiskerLeft K α targetRest) := by
    simpa [W, αe, targetRest, reductionSeq_associator_target_in_Theory2, d, e] using
      (Theory3.symm K (Theory3.whiskerLeftTrans K α (Theory2.whiskerLeft K β d) e))
  have h3 :
      Theory3 K
        (Theory2.trans K A3 (Theory2.trans K W αe))
        (Theory2.trans K A3 (Theory2.whiskerLeft K α targetRest)) :=
    Theory3.transCongrRight K A3 hRestWhisk
  simpa [reductionSeq_associator_target_in_Theory2, X, targetRest, eStep, d, e, A3, A4, W, αe,
    α, β, γ, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat, reductionSeq_in_Theory1] using
    (Theory3.trans K h0 (Theory3.trans K h1 (Theory3.trans K h2 h3)))

private noncomputable def reductionSeq_associator_target_stepInv_aux_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K
      (reductionSeq_associator_target_in_Theory2 K
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K
        (Theory2.associator K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_in_Theory1 K rest)
          (Theory1.comp K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)))
        (Theory2.whiskerLeft K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_target_in_Theory2 K rest q r))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let β := reductionSeq_in_Theory1 K rest
  let γ := reductionSeq_in_Theory1 K q
  let δ := reductionSeq_in_Theory1 K r
  let d := reductionSeq_comp_in_Theory2 K q r
  let e := reductionSeq_comp_in_Theory2 K rest (ReductionSeq.concat q r)
  let A3 := Theory2.associator K α β (Theory1.comp K γ δ)
  let A4 := Theory2.associator K α β (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))
  let W := Theory2.whiskerLeft K α (Theory2.whiskerLeft K β d)
  let αe := Theory2.whiskerLeft K α e
  let targetRest := reductionSeq_associator_target_in_Theory2 K rest q r
  let X := Theory2.whiskerLeft K (Theory1.comp K α β) d
  let eStep := reductionSeq_comp_in_Theory2 K (ReductionSeq.stepInv s rest) (ReductionSeq.concat q r)
  have hWhisk :
      Theory3 K X
        (Theory2.trans K A3
          (Theory2.trans K W (Theory2.symm K A4))) := by
    simpa [X, A3, A4, W, α, β, γ, δ, d] using
      (Theory3.whiskerLeftComp K α β d)
  have hE :
      Theory3 K eStep
        (Theory2.trans K A4 αe) := by
    simpa [eStep, A4, α, β, e, αe, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
      reductionSeq_in_Theory1] using
      (Theory3.refl K eStep)
  have h0 :
      Theory3 K
        (Theory2.trans K X eStep)
        (Theory2.trans K X (Theory2.trans K A4 αe)) :=
    Theory3.transCongrRight K X hE
  have h1 :
      Theory3 K
        (Theory2.trans K X (Theory2.trans K A4 αe))
        (Theory2.trans K
          (Theory2.trans K A3 (Theory2.trans K W (Theory2.symm K A4)))
          (Theory2.trans K A4 αe)) :=
    Theory3.transCongrLeft K hWhisk (Theory2.trans K A4 αe)
  have hCancelA4 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K A4) (Theory2.trans K A4 αe))
        αe := by
    exact Theory3.trans K
      (Theory3.symm K (Theory3.transAssoc K (Theory2.symm K A4) A4 αe))
      (Theory3.trans K
        (Theory3.transCongrLeft K (Theory3.transLeftCancel K A4) αe)
        (Theory3.transReflLeft K αe))
  have h2_inner :
      Theory3 K
        (Theory2.trans K (Theory2.trans K W (Theory2.symm K A4)) (Theory2.trans K A4 αe))
        (Theory2.trans K W αe) := by
    exact Theory3.trans K
      (Theory3.transAssoc K W (Theory2.symm K A4) (Theory2.trans K A4 αe))
      (Theory3.transCongrRight K W hCancelA4)
  have h2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K A3 (Theory2.trans K W (Theory2.symm K A4)))
          (Theory2.trans K A4 αe))
        (Theory2.trans K A3 (Theory2.trans K W αe)) := by
    exact Theory3.trans K
      (Theory3.transAssoc K A3 (Theory2.trans K W (Theory2.symm K A4)) (Theory2.trans K A4 αe))
      (Theory3.transCongrRight K A3 h2_inner)
  have hRestWhisk :
      Theory3 K
        (Theory2.trans K W αe)
        (Theory2.whiskerLeft K α targetRest) := by
    simpa [W, αe, targetRest, reductionSeq_associator_target_in_Theory2, d, e] using
      (Theory3.symm K (Theory3.whiskerLeftTrans K α (Theory2.whiskerLeft K β d) e))
  have h3 :
      Theory3 K
        (Theory2.trans K A3 (Theory2.trans K W αe))
        (Theory2.trans K A3 (Theory2.whiskerLeft K α targetRest)) :=
    Theory3.transCongrRight K A3 hRestWhisk
  simpa [reductionSeq_associator_target_in_Theory2, X, targetRest, eStep, d, e, A3, A4, W, αe,
    α, β, γ, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat, reductionSeq_in_Theory1] using
    (Theory3.trans K h0 (Theory3.trans K h1 (Theory3.trans K h2 h3)))

/-- Coherent-model middle contraction for the inverse associator step-head
bridge. -/
noncomputable def reductionSeq_associator_middle_stepInv_in_Theory3
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
              (Theory1.comp K.toExtensionalKanComplex
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex
                (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex
            (ReductionSeq.stepInv s rest) q r)
          (Theory2.associator K.toExtensionalKanComplex
            (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))))
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex
          rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let A1 := Theory2.associator K0 α β γ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let A3 := Theory2.associator K0 α β (Theory1.comp K0 γ δ)
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let wrA1 := Theory2.whiskerRight K0 A1 δ
  let αassocRest := Theory2.whiskerLeft K0 α assocRest
  have hPent :
      Theory3 K0
        (Theory2.trans K0 assocStep A3)
        (Theory2.trans K0
          (Theory2.trans K0 wrA1 A2c)
          αassocRest) := by
    simpa [assocStep, assocRest, A1, A2c, A3, wrA1, α, β, γ, δ, αassocRest,
      reductionSeq_associator_in_Theory2, reductionSeq_in_Theory1] using
      (fun ρ => K.pentagonPath3 (α ρ) (β ρ) (γ ρ) (δ ρ))
  have hSymmWr :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ)
        (Theory2.symm K0 wrA1) :=
    Theory3.whiskerRightSymm K0 A1 δ
  have h0 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3)) :=
    Theory3.transCongrLeft K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) hSymmWr)
      (Theory2.trans K0 assocStep A3)
  have h1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest)) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0 (Theory2.symm K0 A2c)
        (Theory2.symm K0 wrA1))
      hPent
  have h2a :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest))) :=
    Theory3.transAssoc K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1)
      (Theory2.trans K0 (Theory2.trans K0 wrA1 A2c) αassocRest)
  have h2b_inner :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 wrA1)
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0 A2c αassocRest) := by
    exact Theory3.trans K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 wrA1)
        (Theory3.transAssoc K0 wrA1 A2c αassocRest))
      (Theory3.trans K0
        (Theory3.symm K0
          (Theory3.transAssoc K0 (Theory2.symm K0 wrA1) wrA1
            (Theory2.trans K0 A2c αassocRest)))
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 wrA1)
            (Theory2.trans K0 A2c αassocRest))
          (Theory3.transReflLeft K0 (Theory2.trans K0 A2c αassocRest))))
  have h2b :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest)))
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest)) :=
    Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h2b_inner
  have h2c :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest))
        αassocRest := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2c) A2c αassocRest))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2c)
          αassocRest)
        (Theory3.transReflLeft K0 αassocRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2a
        (Theory3.trans K0 h2b h2c)))

/-- Coherent-model inverse step-head bridge, assuming the specialized reduced
triangle comparison for the tail composition shell. -/
noncomputable def reductionSeq_comp_associator_stepInvHead_from_triangle_in_Theory3
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hTri :
      let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
      let β := Theory1.comp K.toExtensionalKanComplex
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat rest q)
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let targetRest := reductionSeq_associator_target_in_Theory2 K0 rest q r
  let shellRest := reductionSeq_associator_shell_in_Theory2 K0 rest q r
  let αsource := Theory2.whiskerLeft K0 α sourceRest
  let αassoc := Theory2.whiskerLeft K0 α assocRest
  let αtarget := Theory2.whiskerLeft K0 α targetRest
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r
  let targetStep := reductionSeq_associator_target_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r
  let A2c := Theory2.associator K0 α
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 rest) (reductionSeq_in_Theory1 K0 q))
    (reductionSeq_in_Theory1 K0 r)
  let wrsA1 := Theory2.whiskerRight K0
    (Theory2.symm K0
      (Theory2.associator K0 α
        (reductionSeq_in_Theory1 K0 rest)
        (reductionSeq_in_Theory1 K0 q)))
    (reductionSeq_in_Theory1 K0 r)
  let middlePrefix := Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1
  let A3 := Theory2.associator K0 α
    (reductionSeq_in_Theory1 K0 rest)
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 q) (reductionSeq_in_Theory1 K0 r))
  have hMid0 :
      Theory3 K0
        (Theory2.trans K0 assocStep targetStep)
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget)) :=
    Theory3.transCongrRight K0 assocStep
      (reductionSeq_associator_target_stepInv_aux_in_Theory3 K0 s rest q r)
  have hMid1 :
      Theory3 K0
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget))
        (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 assocStep A3 αtarget)
  have hMid2 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 middlePrefix
          (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget)) :=
    Theory3.transCongrRight K0 middlePrefix (Theory3.trans K0 hMid0 hMid1)
  have hMid3 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix
          (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget))
        (Theory2.trans K0
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3))
          αtarget) :=
    Theory3.symm K0
      (Theory3.transAssoc K0 middlePrefix (Theory2.trans K0 assocStep A3) αtarget)
  have hMid4 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3))
          αtarget)
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.transCongrLeft K0
      (reductionSeq_associator_middle_stepInv_in_Theory3 K s rest q r)
      αtarget
  have hMid :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.trans K0 hMid2 (Theory3.trans K0 hMid3 hMid4)
  have h0 :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r)
        (Theory2.trans K0
          (Theory2.trans K0 αsource middlePrefix)
          (Theory2.trans K0 assocStep targetStep)) :=
    Theory3.transCongrLeft K0
      (reductionSeq_associator_source_stepInv_from_triangle_in_Theory3 K0 s rest q r hTri)
      (Theory2.trans K0 assocStep targetStep)
  have h1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 αsource middlePrefix)
          (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αsource
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))) :=
    Theory3.transAssoc K0 αsource middlePrefix (Theory2.trans K0 assocStep targetStep)
  have h2 :
      Theory3 K0
        (Theory2.trans K0 αsource
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep)))
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget)) :=
    Theory3.transCongrRight K0 αsource hMid
  have h3 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget))
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest))) :=
    Theory3.transCongrRight K0 αsource
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α assocRest targetRest))
  have h4 :
      Theory3 K0
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest)))
        (Theory2.whiskerLeft K0 α shellRest) :=
    Theory3.symm K0
      (Theory3.whiskerLeftTrans K0 α sourceRest
        (Theory2.trans K0 assocRest targetRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3 h4)))

/-- Coherent-model middle contraction for the forward associator step-head
bridge. -/
noncomputable def reductionSeq_associator_middle_step_in_Theory3
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
              (Theory1.comp K.toExtensionalKanComplex
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex
                (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex
            (ReductionSeq.step s rest) q r)
          (Theory2.associator K.toExtensionalKanComplex
            (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))))
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex
          rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let A1 := Theory2.associator K0 α β γ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let A3 := Theory2.associator K0 α β (Theory1.comp K0 γ δ)
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.step s rest) q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let wrA1 := Theory2.whiskerRight K0 A1 δ
  let αassocRest := Theory2.whiskerLeft K0 α assocRest
  have hPent :
      Theory3 K0
        (Theory2.trans K0 assocStep A3)
        (Theory2.trans K0
          (Theory2.trans K0 wrA1 A2c)
          αassocRest) := by
    simpa [assocStep, assocRest, A1, A2c, A3, wrA1, α, β, γ, δ, αassocRest,
      reductionSeq_associator_in_Theory2, reductionSeq_in_Theory1] using
      (fun ρ => K.pentagonPath3 (α ρ) (β ρ) (γ ρ) (δ ρ))
  have hSymmWr :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ)
        (Theory2.symm K0 wrA1) :=
    Theory3.whiskerRightSymm K0 A1 δ
  have h0 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3)) :=
    Theory3.transCongrLeft K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) hSymmWr)
      (Theory2.trans K0 assocStep A3)
  have h1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest)) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0 (Theory2.symm K0 A2c)
        (Theory2.symm K0 wrA1))
      hPent
  have h2a :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest))) :=
    Theory3.transAssoc K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1)
      (Theory2.trans K0 (Theory2.trans K0 wrA1 A2c) αassocRest)
  have h2b_inner :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 wrA1)
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0 A2c αassocRest) := by
    exact Theory3.trans K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 wrA1)
        (Theory3.transAssoc K0 wrA1 A2c αassocRest))
      (Theory3.trans K0
        (Theory3.symm K0
          (Theory3.transAssoc K0 (Theory2.symm K0 wrA1) wrA1
            (Theory2.trans K0 A2c αassocRest)))
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 wrA1)
            (Theory2.trans K0 A2c αassocRest))
          (Theory3.transReflLeft K0 (Theory2.trans K0 A2c αassocRest))))
  have h2b :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest)))
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest)) :=
    Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h2b_inner
  have h2c :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest))
        αassocRest := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2c) A2c αassocRest))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2c)
          αassocRest)
        (Theory3.transReflLeft K0 αassocRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2a
        (Theory3.trans K0 h2b h2c)))

/-- Coherent-model forward step-head bridge, assuming the specialized reduced
triangle comparison for the tail composition shell. -/
noncomputable def reductionSeq_comp_associator_stepHead_from_triangle_in_Theory3
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hTri :
      let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
      let β := Theory1.comp K.toExtensionalKanComplex
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat rest q)
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let targetRest := reductionSeq_associator_target_in_Theory2 K0 rest q r
  let shellRest := reductionSeq_associator_shell_in_Theory2 K0 rest q r
  let αsource := Theory2.whiskerLeft K0 α sourceRest
  let αassoc := Theory2.whiskerLeft K0 α assocRest
  let αtarget := Theory2.whiskerLeft K0 α targetRest
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.step s rest) q r
  let targetStep := reductionSeq_associator_target_in_Theory2 K0 (ReductionSeq.step s rest) q r
  let A2c := Theory2.associator K0 α
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 rest) (reductionSeq_in_Theory1 K0 q))
    (reductionSeq_in_Theory1 K0 r)
  let wrsA1 := Theory2.whiskerRight K0
    (Theory2.symm K0
      (Theory2.associator K0 α
        (reductionSeq_in_Theory1 K0 rest)
        (reductionSeq_in_Theory1 K0 q)))
    (reductionSeq_in_Theory1 K0 r)
  let middlePrefix := Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1
  let A3 := Theory2.associator K0 α
    (reductionSeq_in_Theory1 K0 rest)
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 q) (reductionSeq_in_Theory1 K0 r))
  have hMid0 :
      Theory3 K0
        (Theory2.trans K0 assocStep targetStep)
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget)) :=
    Theory3.transCongrRight K0 assocStep
      (reductionSeq_associator_target_step_in_Theory3 K0 s rest q r)
  have hMid1 :
      Theory3 K0
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget))
        (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 assocStep A3 αtarget)
  have hMid2 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 middlePrefix
          (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget)) :=
    Theory3.transCongrRight K0 middlePrefix (Theory3.trans K0 hMid0 hMid1)
  have hMid3 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix
          (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget))
        (Theory2.trans K0
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3))
          αtarget) :=
    Theory3.symm K0
      (Theory3.transAssoc K0 middlePrefix (Theory2.trans K0 assocStep A3) αtarget)
  have hMid4 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3))
          αtarget)
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.transCongrLeft K0
      (reductionSeq_associator_middle_step_in_Theory3 K s rest q r)
      αtarget
  have hMid :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.trans K0 hMid2 (Theory3.trans K0 hMid3 hMid4)
  have h0 :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.step s rest) q r)
        (Theory2.trans K0
          (Theory2.trans K0 αsource middlePrefix)
          (Theory2.trans K0 assocStep targetStep)) :=
    Theory3.transCongrLeft K0
      (reductionSeq_associator_source_step_from_triangle_in_Theory3 K0 s rest q r hTri)
      (Theory2.trans K0 assocStep targetStep)
  have h1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 αsource middlePrefix)
          (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αsource
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))) :=
    Theory3.transAssoc K0 αsource middlePrefix (Theory2.trans K0 assocStep targetStep)
  have h2 :
      Theory3 K0
        (Theory2.trans K0 αsource
          (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep)))
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget)) :=
    Theory3.transCongrRight K0 αsource hMid
  have h3 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget))
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest))) :=
    Theory3.transCongrRight K0 αsource
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α assocRest targetRest))
  have h4 :
      Theory3 K0
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest)))
        (Theory2.whiskerLeft K0 α shellRest) :=
    Theory3.symm K0
      (Theory3.whiskerLeftTrans K0 α sourceRest
        (Theory2.trans K0 assocRest targetRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3 h4)))

/-- Inverse-step analogue of `reductionSeq_associator_target_step_in_Theory3`. -/
noncomputable def reductionSeq_associator_target_stepInv_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K
      (reductionSeq_associator_target_in_Theory2 K
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K
        (Theory2.associator K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_in_Theory1 K rest)
          (Theory1.comp K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)))
        (Theory2.whiskerLeft K
          (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_target_in_Theory2 K rest q r))) := by
  let α := betaEtaStepInv_in_Theory1 K L M s
  let β := reductionSeq_in_Theory1 K rest
  let γ := reductionSeq_in_Theory1 K q
  let δ := reductionSeq_in_Theory1 K r
  let d := reductionSeq_comp_in_Theory2 K q r
  let e := reductionSeq_comp_in_Theory2 K rest (ReductionSeq.concat q r)
  let A3 := Theory2.associator K α β (Theory1.comp K γ δ)
  let A4 := Theory2.associator K α β (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))
  let W := Theory2.whiskerLeft K α (Theory2.whiskerLeft K β d)
  let αe := Theory2.whiskerLeft K α e
  let targetRest := reductionSeq_associator_target_in_Theory2 K rest q r
  let X := Theory2.whiskerLeft K (Theory1.comp K α β) d
  let eStep := reductionSeq_comp_in_Theory2 K (ReductionSeq.stepInv s rest) (ReductionSeq.concat q r)
  have hWhisk :
      Theory3 K X
        (Theory2.trans K A3
          (Theory2.trans K W (Theory2.symm K A4))) := by
    simpa [X, A3, A4, W, α, β, γ, δ, d] using
      (Theory3.whiskerLeftComp K α β d)
  have hE :
      Theory3 K eStep
        (Theory2.trans K A4 αe) := by
    simpa [eStep, A4, α, β, e, αe, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
      reductionSeq_in_Theory1] using
      (Theory3.refl K eStep)
  have h0 :
      Theory3 K
        (Theory2.trans K X eStep)
        (Theory2.trans K X (Theory2.trans K A4 αe)) :=
    Theory3.transCongrRight K X hE
  have h1 :
      Theory3 K
        (Theory2.trans K X (Theory2.trans K A4 αe))
        (Theory2.trans K
          (Theory2.trans K A3 (Theory2.trans K W (Theory2.symm K A4)))
          (Theory2.trans K A4 αe)) :=
    Theory3.transCongrLeft K hWhisk (Theory2.trans K A4 αe)
  have hCancelA4 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K A4) (Theory2.trans K A4 αe))
        αe := by
    exact Theory3.trans K
      (Theory3.symm K (Theory3.transAssoc K (Theory2.symm K A4) A4 αe))
      (Theory3.trans K
        (Theory3.transCongrLeft K (Theory3.transLeftCancel K A4) αe)
        (Theory3.transReflLeft K αe))
  have h2_inner :
      Theory3 K
        (Theory2.trans K (Theory2.trans K W (Theory2.symm K A4)) (Theory2.trans K A4 αe))
        (Theory2.trans K W αe) := by
    exact Theory3.trans K
      (Theory3.transAssoc K W (Theory2.symm K A4) (Theory2.trans K A4 αe))
      (Theory3.transCongrRight K W hCancelA4)
  have h2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K A3 (Theory2.trans K W (Theory2.symm K A4)))
          (Theory2.trans K A4 αe))
        (Theory2.trans K A3 (Theory2.trans K W αe)) := by
    exact Theory3.trans K
      (Theory3.transAssoc K A3 (Theory2.trans K W (Theory2.symm K A4)) (Theory2.trans K A4 αe))
      (Theory3.transCongrRight K A3 h2_inner)
  have hRestWhisk :
      Theory3 K
        (Theory2.trans K W αe)
        (Theory2.whiskerLeft K α targetRest) := by
    simpa [W, αe, targetRest, reductionSeq_associator_target_in_Theory2, d, e] using
      (Theory3.symm K (Theory3.whiskerLeftTrans K α (Theory2.whiskerLeft K β d) e))
  have h3 :
      Theory3 K
        (Theory2.trans K A3 (Theory2.trans K W αe))
        (Theory2.trans K A3 (Theory2.whiskerLeft K α targetRest)) :=
    Theory3.transCongrRight K A3 hRestWhisk
  simpa [reductionSeq_associator_target_in_Theory2, X, targetRest, eStep, d, e, A3, A4, W, αe,
    α, β, γ, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat, reductionSeq_in_Theory1] using
    (Theory3.trans K h0 (Theory3.trans K h1 (Theory3.trans K h2 h3)))

/-- Base case of the associator comparison: when the left explicit path is
reflexive, the structural associator shell collapses to the equality-generated
semantic associator via left-unitor naturality and left-unitor-on-composites. -/
noncomputable def reductionSeq_comp_associator_refl_in_Theory3
    (K : ExtensionalKanComplex) {M N P : Term}
    (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r)
      (Theory2.ofEq K
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r))) := by
  change Theory3 K
    (Theory2.trans K
      (Theory2.trans K
        (Theory2.symm K
          (reductionSeq_comp_in_Theory2 K ((ReductionSeq.refl M).concat q) r))
        (Theory2.whiskerRight K
          (Theory2.symm K
            (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)))
          (reductionSeq_in_Theory1 K r)))
      (Theory2.trans K
        (Theory2.associator K (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
          (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
        (Theory2.trans K
          (Theory2.whiskerLeft K
            (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
            (reductionSeq_comp_in_Theory2 K q r))
          (Theory2.leftUnitor K
            (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))))))
    (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))
  let c := reductionSeq_comp_in_Theory2 K q r
  let lu := Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
  have hNat :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c)
          (Theory2.leftUnitor K (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))))
        (Theory2.trans K
          (Theory2.leftUnitor K
            (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)))
          c) :=
    reductionSeq_leftUnitorNaturality_in_Theory3 K q r
  have hComp :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K (Theory1.refl K M)
            (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
          (Theory2.leftUnitor K
            (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))))
        (Theory2.whiskerRight K
          (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))
          (reductionSeq_in_Theory1 K r)) :=
    reductionSeq_leftUnitorComp_in_Theory3 K q r
  have hInnerCore :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K (Theory1.refl K M)
            (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
          (Theory2.trans K
            (Theory2.whiskerLeft K (Theory1.refl K M) c)
            (Theory2.leftUnitor K
              (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))))
        (Theory2.trans K
          (Theory2.whiskerRight K lu (reductionSeq_in_Theory1 K r))
          c) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K
        (Theory2.associator K (Theory1.refl K M)
          (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
        hNat)
      (Theory3.trans K
        (Theory3.symm K
          (Theory3.transAssoc K
            (Theory2.associator K (Theory1.refl K M)
              (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
            (Theory2.leftUnitor K
              (Theory1.comp K (reductionSeq_in_Theory1 K q)
                (reductionSeq_in_Theory1 K r)))
            c))
        (Theory3.transCongrLeft K hComp c))
  have hCancelLu :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r))
          (Theory2.trans K
            (Theory2.whiskerRight K lu (reductionSeq_in_Theory1 K r))
            c))
        c := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K
          (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r))
          (Theory2.whiskerRight K lu (reductionSeq_in_Theory1 K r))
          c))
      (Theory3.trans K
        (Theory3.transCongrLeft K
          (Theory3.whiskerRightLeftCancel K lu (reductionSeq_in_Theory1 K r))
          c)
        (Theory3.transReflLeft K c))
  have hInner :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r))
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M)
              (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c)
              (Theory2.leftUnitor K
                (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))))))
        c := by
    exact Theory3.trans K
      (Theory3.transCongrRight K
        (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r))
        hInnerCore)
      hCancelLu
  let c0 := reductionSeq_comp_in_Theory2 K ((ReductionSeq.refl M).concat q) r
  have hCancel :
      Theory3 K
        (Theory2.trans K (Theory2.symm K c0) c)
        (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))) := by
    simpa [ReductionSeq.concat, c0, c] using
      (Theory3.transLeftCancel K c)
  have hOuterAssoc :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c0)
            (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r)))
          (Theory2.trans K
            (Theory2.associator K (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
              (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
            (Theory2.trans K
              (Theory2.whiskerLeft K
                (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
                c)
              (Theory2.leftUnitor K
                (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))))))
        (Theory2.trans K (Theory2.symm K c0)
          (Theory2.trans K
            (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r))
            (Theory2.trans K
              (Theory2.associator K (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
                (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
              (Theory2.trans K
                (Theory2.whiskerLeft K
                  (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
                  c)
                (Theory2.leftUnitor K
                  (reductionSeq_in_Theory1 K (ReductionSeq.concat q r))))))) :=
    Theory3.transAssoc K
      (Theory2.symm K c0)
      (Theory2.whiskerRight K (Theory2.symm K lu) (reductionSeq_in_Theory1 K r))
      (Theory2.trans K
        (Theory2.associator K (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
          (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
        (Theory2.trans K
          (Theory2.whiskerLeft K
            (reductionSeq_in_Theory1 K (ReductionSeq.refl M))
            c)
          (Theory2.leftUnitor K
            (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))))
  exact Theory3.trans K
    hOuterAssoc
    (Theory3.trans K
      (Theory3.transCongrRight K (Theory2.symm K c0) hInner)
      hCancel)

/-- Final bookkeeping step for the recursive associator comparison when the
left explicit path begins with a forward βη step.

The only remaining input is a `head` bridge that contracts the full structural
associator shell for `step s rest` to the left whisker of the tail shell. Once
that geometric normalization is available, the inductive hypothesis closes the
step by `Theory3.whiskerLeftCongrOfEq`. -/
noncomputable def reductionSeq_comp_associator_step_finish_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (ih :
      Theory3 K
        (reductionSeq_associator_shell_in_Theory2 K rest q r)
        (Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (ReductionSeq.concat_assoc rest q r))))
    (head :
      Theory3 K
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.step s rest) q r)
        (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K L M s)
          (reductionSeq_associator_shell_in_Theory2 K rest q r))) :
    Theory3 K
      (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.step s rest) q r)
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s rest) q r))) := by
  let hRest :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (ReductionSeq.concat_assoc rest q r)
  exact Theory3.trans K head
    (Theory3.whiskerLeftCongrOfEq K (betaEtaStep_in_Theory1 K L M s) hRest ih)

/-- Final bookkeeping step for the recursive associator comparison when the
left explicit path begins with an inverse βη step. This is the inverse-step
analogue of `reductionSeq_comp_associator_step_finish_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_stepInv_finish_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (ih :
      Theory3 K
        (reductionSeq_associator_shell_in_Theory2 K rest q r)
        (Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (ReductionSeq.concat_assoc rest q r))))
    (head :
      Theory3 K
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.stepInv s rest) q r)
        (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K L M s)
          (reductionSeq_associator_shell_in_Theory2 K rest q r))) :
    Theory3 K
      (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.stepInv s rest) q r)
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s rest) q r))) := by
  let hRest :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (ReductionSeq.concat_assoc rest q r)
  exact Theory3.trans K head
    (Theory3.whiskerLeftCongrOfEq K (betaEtaStepInv_in_Theory1 K L M s) hRest ih)

/-- Recursive associator comparison, parameterized by the still-missing head
bridges for forward and inverse leading βη steps.

This packages the entire recursion and bookkeeping layer now, so the remaining
geometric frontier is exactly the local step-head normalization. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_of_heads
    (K : ExtensionalKanComplex)
    (stepHead :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        Theory3 K
          (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.step s rest) q r)
          (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K L M s)
            (reductionSeq_associator_shell_in_Theory2 K rest q r)))
    (stepInvHead :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        Theory3 K
          (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.stepInv s rest) q r)
          (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K L M s)
            (reductionSeq_associator_shell_in_Theory2 K rest q r))) :
    {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      (r : ReductionSeq N P) →
      Theory3 K
        (reductionSeq_associator_shell_in_Theory2 K p q r)
        (Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (ReductionSeq.concat_assoc p q r)))
  | _, _, _, _, .refl M, q, r =>
      reductionSeq_comp_associator_refl_in_Theory3 K q r
  | _, _, _, _, .step s rest, q, r =>
      reductionSeq_comp_associator_step_finish_in_Theory3 K s rest q r
        (reductionSeq_comp_associator_in_Theory3_of_heads K stepHead stepInvHead rest q r)
        (stepHead s rest q r)
  | _, _, _, _, .stepInv s rest, q, r =>
      reductionSeq_comp_associator_stepInv_finish_in_Theory3 K s rest q r
        (reductionSeq_comp_associator_in_Theory3_of_heads K stepHead stepInvHead rest q r)
        (stepInvHead s rest q r)

/-- Recursive associator comparison, parameterized by the exact remaining
midpoint/front seed witnesses on forward and inverse leading steps.

Once the source-side `hMidFront` witnesses are supplied, the exact reduced
triangle witnesses, local head bridges, and the full recursive associator
comparison all follow automatically on the bare `ExtensionalKanComplex`
interface. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_of_midFronts
    (K : CoherentExtensionalKanComplex)
    (stepMidFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
              (α ρ) (γ ρ) (δ ρ)))
    (stepInvMidFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
              (α ρ) (γ ρ) (δ ρ))) :
    {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      (r : ReductionSeq N P) →
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc p q r))) := by
  let K0 := K.toExtensionalKanComplex
  have stepHead :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        Theory3 K0
          (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.step s rest) q r)
          (Theory2.whiskerLeft K0 (betaEtaStep_in_Theory1 K0 L M s)
            (reductionSeq_associator_shell_in_Theory2 K0 rest q r)) := by
    intro L M N P Q s rest q r
    exact reductionSeq_comp_associator_stepHead_from_triangle_in_Theory3 K s rest q r
      (reductionSeq_comp_triangle_target_step_in_Theory3 K0 s rest q r
        (stepMidFront s rest q r))
  have stepInvHead :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        Theory3 K0
          (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r)
          (Theory2.whiskerLeft K0 (betaEtaStepInv_in_Theory1 K0 L M s)
            (reductionSeq_associator_shell_in_Theory2 K0 rest q r)) := by
    intro L M N P Q s rest q r
    exact reductionSeq_comp_associator_stepInvHead_from_triangle_in_Theory3 K s rest q r
      (reductionSeq_comp_triangle_target_stepInv_in_Theory3 K0 s rest q r
         (stepInvMidFront s rest q r))
  intro L M N P p q r
  exact reductionSeq_comp_associator_in_Theory3_of_heads K0 stepHead stepInvHead p q r

/-- Recursive associator comparison, parameterized by the smaller remaining
WLWR front-loop contractions on forward and inverse leading steps.

This sharpens `reductionSeq_comp_associator_in_Theory3_of_midFronts`: once the
direct WLWR front loops contract, the exact midpoint/front seed witnesses and
hence the full recursive associator comparison follow automatically. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_of_frontContracts
    (K : CoherentExtensionalKanComplex)
    (stepFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.refl K.toExtensionalKanComplex
            (Theory1.refl K.toExtensionalKanComplex Q)))
    (stepInvFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.refl K.toExtensionalKanComplex
            (Theory1.refl K.toExtensionalKanComplex Q))) :
    {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      (r : ReductionSeq N P) →
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc p q r))) := by
  let K0 := K.toExtensionalKanComplex
  have stepMidFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
              (α ρ) (γ ρ) (δ ρ)) := by
    intro L M N P Q s rest q r
    let α := betaEtaStep_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonOfFrontPath3
      K0 α η δ (stepFront s rest q r)
  have stepInvMidFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
              (α ρ) (γ ρ) (δ ρ)) := by
    intro L M N P Q s rest q r
    let α := betaEtaStepInv_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonOfFrontPath3
      K0 α η δ (stepInvFront s rest q r)
  intro L M N P p q r
  exact reductionSeq_comp_associator_in_Theory3_of_midFronts K stepMidFront stepInvMidFront p q r

/-- Recursive associator comparison, parameterized by normalized WLWR
right-half comparisons on forward and inverse leading steps.

This sharpens `reductionSeq_comp_associator_in_Theory3_of_rightComparisons`:
once the normalized comparisons `mid ; symm assoc ~ right` are known, the
reduced right-half comparisons, the direct WLWR front loops, the exact
midpoint/front seed witnesses, and hence the full recursive associator
comparison follow automatically. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_of_normalizedRightComparisons
    (K : CoherentExtensionalKanComplex)
    (stepNorm :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ))
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
                (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                  (α ρ) (γ ρ) (δ ρ))))
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)))
    (stepInvNorm :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ))
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
                (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                  (α ρ) (γ ρ) (δ ρ))))
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ))) :
    {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      (r : ReductionSeq N P) →
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc p q r))) := by
  let K0 := K.toExtensionalKanComplex
  have stepRight :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.symmPath2
              (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))) := by
    intro L M N P Q s rest q r
    let α := betaEtaStep_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
      K0 α η δ (stepNorm s rest q r)
  have stepInvRight :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.symmPath2
              (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))) := by
    intro L M N P Q s rest q r
    let α := betaEtaStepInv_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
      K0 α η δ (stepInvNorm s rest q r)
  have stepFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.refl K0 (Theory1.refl K0 Q)) := by
    intro L M N P Q s rest q r
    let α := betaEtaStep_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightFrontContractOfRightPath3
      K0 α η δ (stepRight s rest q r)
  have stepInvFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.refl K0 (Theory1.refl K0 Q)) := by
    intro L M N P Q s rest q r
    let α := betaEtaStepInv_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightFrontContractOfRightPath3
      K0 α η δ (stepInvRight s rest q r)
  intro L M N P p q r
  exact reductionSeq_comp_associator_in_Theory3_of_frontContracts K
    stepFront stepInvFront p q r

/-- Recursive associator comparison, parameterized by the smaller reduced
right-half WLWR comparisons on forward and inverse leading steps.

This sharpens `reductionSeq_comp_associator_in_Theory3_of_frontContracts`: once
the reduced right-half comparisons are known, the direct WLWR front loops, the
exact midpoint/front seed witnesses, and hence the full recursive associator
comparison follow automatically. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_of_rightComparisons
    (K : CoherentExtensionalKanComplex)
    (stepRight :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))
    (stepInvRight :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
        let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
        let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex (ReductionSeq.concat rest q)
        let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
                (α ρ) (η ρ) (δ ρ)).toTriangle
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                  (α ρ) (η ρ))
                (δ ρ)).toTriangle)
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) :
    {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      (r : ReductionSeq N P) →
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc p q r))) := by
  let K0 := K.toExtensionalKanComplex
  have stepFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStep_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.refl K0 (Theory1.refl K0 Q)) := by
    intro L M N P Q s rest q r
    let α := betaEtaStep_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightFrontContractOfRightPath3
      K0 α η δ (stepRight s rest q r)
  have stepInvFront :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        let α := betaEtaStepInv_in_Theory1 K0 L M s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        Theory3 K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidRightFrontPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.refl K0 (Theory1.refl K0 Q)) := by
    intro L M N P Q s rest q r
    let α := betaEtaStepInv_in_Theory1 K0 L M s
    let η := reductionSeq_comp_in_Theory2 K0 rest q
    let δ := reductionSeq_in_Theory1 K0 r
    exact Theory3.whiskerLeftWhiskerRightFrontContractOfRightPath3
      K0 α η δ (stepInvRight s rest q r)
  intro L M N P p q r
  exact reductionSeq_comp_associator_in_Theory3_of_frontContracts K
    stepFront stepInvFront p q r

/-- Any recursive associator-shell comparison `shell ~ ofEq concat_assoc`
immediately upgrades the interpreted equality-generated associator 2-cell to the
structural associator shell. -/
noncomputable def homotopy2_associator_bridge_in_Theory3_of_compAssociator
    (K : ExtensionalKanComplex)
    (hAssocComp :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (reductionSeq_associator_shell_in_Theory2 K p q r)
          (Theory2.ofEq K
            (congrArg (fun u => reductionSeq_in_Theory1 K u)
              (ReductionSeq.concat_assoc p q r))))
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
      (reductionSeq_associator_shell_in_Theory2 K p q r) := by
  have hInterp :
      homotopy2_in_Theory2 K (HigherTerms.associator p q r) =
        Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (ReductionSeq.concat_assoc p q r)) :=
    homotopy2_in_Theory2_ofEq K (ReductionSeq.concat_assoc p q r)
  exact hInterp ▸ Theory3.symm K (hAssocComp p q r)

/-- The smaller nested-whisker comparison
`assoc ; whiskerLeft (whiskerRight η δ) ; symm assoc ~ right` already implies the
normalized WLWR comparison `mid ; symm assoc ~ right`. -/
private noncomputable def
    reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term} (α : Theory1 K L M)
    {β γ : Theory1 K M N} (η : Theory2 K β γ) (δ : Theory1 K N P)
    (hNested :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    Theory3 K
      (Theory2.trans K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
            (α ρ) (η ρ) (δ ρ))
        (Theory2.symm K (Theory2.associator K α γ δ)))
      (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ) := by
  have hMidLeft :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ)))
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
            (α ρ) (η ρ) (δ ρ)) := by
    simpa using
      (Theory3.whiskerLeftWhiskerRightMidLeftNormalizedComparison K α η δ)
  have hSourceToNorm :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.trans K
          (fun ρ =>
            K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.symm K (Theory2.associator K α γ δ))) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K
          (Theory2.associator K α β δ)
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
          (Theory2.symm K (Theory2.associator K α γ δ))))
      (Theory3.transCongrLeft K hMidLeft
        (Theory2.symm K (Theory2.associator K α γ δ)))
  exact Theory3.trans K
    (Theory3.symm K hSourceToNorm)
    hNested

/-- The left-whiskered source leg of the reflexive associator shell splits into the
inverse whiskers of the outer composition comparison and the inner right whisker. -/
private noncomputable def
    reductionSeq_comp_associator_refl_sourceWhiskerDecompose_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let δ := reductionSeq_in_Theory1 K r
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    Theory3 K
      (Theory2.whiskerLeft K α
        (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.trans K
        (Theory2.symm K (Theory2.whiskerLeft K α c₀))
        (Theory2.symm K
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K η δ)))) := by
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K r
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  have hTrans :
      Theory3 K
        (Theory2.whiskerLeft K α
          (Theory2.trans K (Theory2.symm K c₀)
            (Theory2.whiskerRight K (Theory2.symm K η) δ)))
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c₀))
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K (Theory2.symm K η) δ))) := by
    simpa [c₀, η, δ, reductionSeq_associator_source_in_Theory2] using
      (Theory3.whiskerLeftTrans K α
        (Theory2.symm K c₀)
        (Theory2.whiskerRight K (Theory2.symm K η) δ))
  have hFirst :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.symm K c₀))
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K (Theory2.symm K η) δ)))
        (Theory2.trans K
          (Theory2.symm K (Theory2.whiskerLeft K α c₀))
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K (Theory2.symm K η) δ))) := by
    exact Theory3.transCongrLeft K
      (Theory3.whiskerLeftSymm K α c₀)
      (Theory2.whiskerLeft K α
        (Theory2.whiskerRight K (Theory2.symm K η) δ))
  have hSecond0 :
      Theory3 K
        (Theory2.whiskerLeft K α
          (Theory2.whiskerRight K (Theory2.symm K η) δ))
        (Theory2.whiskerLeft K α
          (Theory2.symm K (Theory2.whiskerRight K η δ))) := by
    exact Theory3.whiskerLeftCongr K α
      (Theory3.whiskerRightSymm K η δ)
  have hSecond1 :
      Theory3 K
        (Theory2.whiskerLeft K α
          (Theory2.symm K (Theory2.whiskerRight K η δ)))
        (Theory2.symm K
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K η δ))) := by
    exact Theory3.whiskerLeftSymm K α (Theory2.whiskerRight K η δ)
  have hSecond :
      Theory3 K
        (Theory2.whiskerLeft K α
          (Theory2.whiskerRight K (Theory2.symm K η) δ))
        (Theory2.symm K
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K η δ))) := by
    exact Theory3.trans K hSecond0 hSecond1
  have hFinal :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K (Theory2.whiskerLeft K α c₀))
          (Theory2.whiskerLeft K α
            (Theory2.whiskerRight K (Theory2.symm K η) δ)))
        (Theory2.trans K
          (Theory2.symm K (Theory2.whiskerLeft K α c₀))
          (Theory2.symm K
            (Theory2.whiskerLeft K α
              (Theory2.whiskerRight K η δ)))) := by
    exact Theory3.transCongrRight K
      (Theory2.symm K (Theory2.whiskerLeft K α c₀))
        hSecond
  exact Theory3.trans K hTrans (Theory3.trans K hFirst hFinal)

/-- The nested-whisker comparison is equivalent to the cancellation step needed on
the decomposed source leg of the left-whiskered reflexive associator shell. -/
private noncomputable def
    reductionSeq_comp_associator_refl_sourceWhiskerCancel_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    (η : Theory2 K β γ) (δ : Theory1 K N P)
    (hNested :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    Theory3 K
      (Theory2.symm K
        (Theory2.whiskerLeft K α
          (Theory2.whiskerRight K η δ)))
      (Theory2.trans K
        (Theory2.symm K (Theory2.associator K α γ δ))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ))
          (Theory2.associator K α β δ))) := by
  let Aβ := Theory2.associator K α β δ
  let Aγ := Theory2.associator K α γ δ
  let left := Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ)
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  have hPre :
      Theory3 K
        (Theory2.trans K (Theory2.symm K Aβ)
          (Theory2.trans K Aβ
            (Theory2.trans K left (Theory2.symm K Aγ))))
        (Theory2.trans K (Theory2.symm K Aβ) right) := by
    simpa [Aβ, Aγ, left, right] using
      (Theory3.transCongrRight K (Theory2.symm K Aβ) hNested)
  have hPreSource :
      Theory3 K
        (Theory2.trans K (Theory2.symm K Aβ)
          (Theory2.trans K Aβ
            (Theory2.trans K left (Theory2.symm K Aγ))))
        (Theory2.trans K left (Theory2.symm K Aγ)) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K Aβ) Aβ
          (Theory2.trans K left (Theory2.symm K Aγ))))
      (Theory3.trans K
        (Theory3.transCongrLeft K
          (Theory3.transLeftCancel K Aβ)
          (Theory2.trans K left (Theory2.symm K Aγ)))
        (Theory3.transReflLeft K
          (Theory2.trans K left (Theory2.symm K Aγ))))
  have h1 :
      Theory3 K
        (Theory2.trans K left (Theory2.symm K Aγ))
        (Theory2.trans K (Theory2.symm K Aβ) right) := by
    exact Theory3.trans K
      (Theory3.symm K hPreSource)
      hPre
  have hPost :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K left (Theory2.symm K Aγ))
          Aγ)
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K Aβ) right)
          Aγ) := by
    exact Theory3.transCongrLeft K h1 Aγ
  have hPostSource :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K left (Theory2.symm K Aγ))
          Aγ)
        left := by
    exact Theory3.trans K
      (Theory3.transAssoc K left (Theory2.symm K Aγ) Aγ)
      (Theory3.trans K
        (Theory3.transCongrRight K left
          (Theory3.transLeftCancel K Aγ))
        (Theory3.transReflRight K left))
  have h2 :
      Theory3 K
        left
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K Aβ) right)
          Aγ) := by
    exact Theory3.trans K
      (Theory3.symm K hPostSource)
      hPost
  have h2symm :
      Theory3 K
        (Theory2.symm K
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K Aβ) right)
            Aγ))
        (Theory2.symm K left) := by
    exact Theory3.symm K (Theory3.symmCongr K h2)
  have hExpand :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K Aγ)
          (Theory2.trans K (Theory2.symm K right) Aβ))
        (Theory2.symm K
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K Aβ) right)
            Aγ)) := by
    have hInnerExpand :
        Theory3 K
          (Theory2.trans K (Theory2.symm K right) Aβ)
          (Theory2.symm K
            (Theory2.trans K (Theory2.symm K Aβ) right)) := by
      exact Theory3.trans K
        (Theory3.transCongrRight K (Theory2.symm K right)
          (Theory3.symm K (Theory3.symmSymm K Aβ)))
        (Theory3.symm K
          (Theory3.symmTrans K (Theory2.symm K Aβ) right))
    exact Theory3.trans K
      (Theory3.transCongrRight K (Theory2.symm K Aγ) hInnerExpand)
      (Theory3.symm K
        (Theory3.symmTrans K
          (Theory2.trans K (Theory2.symm K Aβ) right) Aγ))
  exact Theory3.symm K (Theory3.trans K hExpand h2symm)

/-- Public wrapper around the source-side cancellation form produced by a nested
whisker comparison
`assoc ; whiskerLeft (whiskerRight η δ) ; symm assoc ~ right`.

This packages the exact post-`simp` refl/source goal: once the smaller nested
comparison is available, the remaining conjugation step is purely algebraic. -/
noncomputable def
    reductionSeq_comp_associator_refl_sourceWhiskerCancel_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    (η : Theory2 K β γ) (δ : Theory1 K N P)
    (hNested :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    Theory3 K
      (Theory2.symm K
        (Theory2.whiskerLeft K α
          (Theory2.whiskerRight K η δ)))
      (Theory2.trans K
        (Theory2.symm K (Theory2.associator K α γ δ))
        (Theory2.trans K
          (Theory2.symm K
            (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ))
          (Theory2.associator K α β δ))) := by
  simpa using
    (reductionSeq_comp_associator_refl_sourceWhiskerCancel_in_Theory3
      K α η δ hNested)

/-- Once the smaller nested-whisker comparison is known, the left-whiskered source
leg of the reflexive associator shell already splits into the conjugation form
used by the source-side bridge probes. -/
private noncomputable def
    reductionSeq_comp_associator_refl_sourceWhiskerSplit_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.whiskerLeft K α
        (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.trans K
        (Theory2.symm K T)
        (Theory2.trans K (Theory2.symm K right) Aβ)) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let left := Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ)
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let T := Theory2.trans K
    (Theory2.associator K α γ δ)
    (Theory2.whiskerLeft K α c₀)
  have hDecompose :
      Theory3 K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
        (Theory2.trans K
          (Theory2.symm K (Theory2.whiskerLeft K α c₀))
          (Theory2.symm K left)) := by
    simpa [η, δ, c₀, left] using
      (reductionSeq_comp_associator_refl_sourceWhiskerDecompose_in_Theory3 K α q r)
  have hCancel :
      Theory3 K
        (Theory2.symm K left)
        (Theory2.trans K
          (Theory2.symm K (Theory2.associator K α γ δ))
          (Theory2.trans K (Theory2.symm K right) Aβ)) := by
    simpa [Aβ, left, right, γ] using
      (reductionSeq_comp_associator_refl_sourceWhiskerCancel_in_Theory3
        K α η δ hNested)
  have hTarget :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K (Theory2.whiskerLeft K α c₀))
          (Theory2.symm K left))
        (Theory2.trans K
          (Theory2.symm K T)
          (Theory2.trans K (Theory2.symm K right) Aβ)) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K
        (Theory2.symm K (Theory2.whiskerLeft K α c₀))
        hCancel)
      (Theory3.trans K
        (Theory3.symm K
          (Theory3.transAssoc K
            (Theory2.symm K (Theory2.whiskerLeft K α c₀))
            (Theory2.symm K (Theory2.associator K α γ δ))
            (Theory2.trans K (Theory2.symm K right) Aβ)))
        (Theory3.transCongrLeft K
          (Theory3.symm K
            (Theory3.symmTrans K
              (Theory2.associator K α γ δ)
              (Theory2.whiskerLeft K α c₀)))
          (Theory2.trans K (Theory2.symm K right) Aβ)))
  exact Theory3.trans K hDecompose hTarget

/-- Public wrapper exposing the full refl/source split once the smaller nested
whisker comparison
`assoc ; whiskerLeft (whiskerRight leftUnitor δ) ; symm assoc ~ right`
has been established. -/
noncomputable def
    reductionSeq_comp_associator_refl_sourceWhiskerSplit_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.whiskerLeft K α
        (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.trans K
        (Theory2.symm K T)
        (Theory2.trans K (Theory2.symm K right) Aβ)) := by
  simpa using
    (reductionSeq_comp_associator_refl_sourceWhiskerSplit_of_nestedWhiskerComparison
      K α q r hNested)

/-- Appending the structural left-unitor shell to the refl target leg factors the
entire target side through the right-whiskered semantic left unitor, before any
comparison between `comp_in refl q` and `leftUnitor q` is used. -/
noncomputable def reductionSeq_comp_associator_refl_targetWhiskerFactor_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let luRight := Theory2.whiskerRight K
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ
    Theory3 K
      (Theory2.trans K Aβ
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
              (Theory2.trans K e
                (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
      (Theory2.trans K
        (Theory2.trans K Aβ (Theory2.whiskerLeft K α luRight))
        (Theory2.whiskerLeft K α c₀)) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let luRight := Theory2.whiskerRight K
    (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ
  have hFactor :
      Theory3 K
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
              (Theory2.trans K e
                (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r))))))
        (Theory2.whiskerLeft K α (Theory2.trans K luRight c₀)) := by
    simpa [δ, c₀, e, luRight] using
      (Theory3.whiskerLeftCongr K α
        (reductionSeq_leftUnitorCompShell_in_Theory3 K q r))
  have hSplit :
      Theory3 K
        (Theory2.whiskerLeft K α (Theory2.trans K luRight c₀))
        (Theory2.trans K
          (Theory2.whiskerLeft K α luRight)
          (Theory2.whiskerLeft K α c₀)) := by
    exact Theory3.whiskerLeftTrans K α luRight c₀
  exact Theory3.trans K
    (Theory3.transCongrRight K Aβ hFactor)
    (Theory3.trans K
      (Theory3.transCongrRight K Aβ hSplit)
      (Theory3.symm K
        (Theory3.transAssoc K Aβ
          (Theory2.whiskerLeft K α luRight)
          (Theory2.whiskerLeft K α c₀))))

/-- If the reduced triangle comparison for the left-unitor specialization is
available, then the remaining left-unitor head comparison follows by pure
associativity/cancellation algebra. -/
noncomputable def
    reductionSeq_comp_associator_refl_leftUnitorHeadComparison_in_Theory3_of_triangleComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hTri :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      let η := Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
          (Theory2.symm K (Theory2.associator K α γ δ)))) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let η := Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
    let luRight := Theory2.whiskerRight K η δ
    let head := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K α β δ)
        (Theory2.whiskerLeft K α luRight))
      (Theory2.trans K head
        (Theory2.associator K α γ δ)) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let η := Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
  let luRight := Theory2.whiskerRight K η δ
  let head := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  have hWLWR :
      Theory3 K
        head
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α luRight)
            (Theory2.symm K (Theory2.associator K α γ δ)))) := by
    simpa [η, luRight, head] using
      (Theory3.whiskerLeftWhiskerRightFromTriangleComparison K α η δ hTri)
  have hAssocHead :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.associator K α β δ)
            (Theory2.whiskerLeft K α luRight))
          (Theory2.symm K (Theory2.associator K α γ δ)))
        head := by
    exact Theory3.trans K
      (Theory3.transAssoc K
        (Theory2.associator K α β δ)
        (Theory2.whiskerLeft K α luRight)
        (Theory2.symm K (Theory2.associator K α γ δ)))
      (Theory3.symm K hWLWR)
  have hHeadExpand :
      Theory3 K
        head
        (Theory2.trans K
          (Theory2.trans K head (Theory2.associator K α γ δ))
          (Theory2.symm K (Theory2.associator K α γ δ))) := by
    exact Theory3.symm K <| Theory3.trans K
      (Theory3.transAssoc K head
        (Theory2.associator K α γ δ)
        (Theory2.symm K (Theory2.associator K α γ δ)))
      (Theory3.trans K
        (Theory3.transCongrRight K head
          (Theory3.transRightCancel K (Theory2.associator K α γ δ)))
        (Theory3.transReflRight K head))
  exact Theory3.transRightCancelCongr K
    (Theory2.symm K (Theory2.associator K α γ δ)) <|
      Theory3.trans K hAssocHead hHeadExpand

/-- Public wrapper exposing the refl/target split once the remaining left-unitor
head comparison
`assoc ; whiskerLeft (whiskerRight leftUnitor δ)
 ~ whiskerRight (whiskerLeft leftUnitor) δ ; assoc`
has been established. -/
noncomputable def
    reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_leftUnitorHeadComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hHead :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      let luRight := Theory2.whiskerRight K
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ
      let head := Theory2.whiskerRight K
        (Theory2.whiskerLeft K α
          (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.whiskerLeft K α luRight))
        (Theory2.trans K head
          (Theory2.associator K α γ δ))) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let head := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.trans K Aβ
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
              (Theory2.trans K e
                (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
      (Theory2.trans K head T) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let luRight := Theory2.whiskerRight K
    (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ
  let head := Theory2.whiskerRight K
    (Theory2.whiskerLeft K α
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
  let T := Theory2.trans K
    (Theory2.associator K α γ δ)
    (Theory2.whiskerLeft K α c₀)
  have hFactor :
      Theory3 K
        (Theory2.trans K Aβ
          (Theory2.whiskerLeft K α
            (Theory2.trans K
              (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
              (Theory2.trans K
                (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
                (Theory2.trans K e
                  (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
        (Theory2.trans K
          (Theory2.trans K Aβ (Theory2.whiskerLeft K α luRight))
          (Theory2.whiskerLeft K α c₀)) := by
    simpa [β, δ, Aβ, c₀, e, luRight] using
      (reductionSeq_comp_associator_refl_targetWhiskerFactor_in_Theory3 K α q r)
  have hHead' :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K Aβ (Theory2.whiskerLeft K α luRight))
          (Theory2.whiskerLeft K α c₀))
        (Theory2.trans K
          (Theory2.trans K head (Theory2.associator K α γ δ))
          (Theory2.whiskerLeft K α c₀)) := by
    exact Theory3.transCongrLeft K hHead (Theory2.whiskerLeft K α c₀)
  exact Theory3.trans K hFactor
    (Theory3.trans K hHead'
      (Theory3.transAssoc K head
        (Theory2.associator K α γ δ)
        (Theory2.whiskerLeft K α c₀)))

/-- Public wrapper exposing the whole refl/target split once the remaining
left-unitor reduced triangle comparison has been established. -/
noncomputable def
    reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_leftUnitorTriangleComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hTri :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      let η := Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
          (Theory2.symm K (Theory2.associator K α γ δ)))) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let head := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.trans K Aβ
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
              (Theory2.trans K e
                (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
      (Theory2.trans K head T) := by
  simpa using
    (reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_leftUnitorHeadComparison
      K α q r
      (reductionSeq_comp_associator_refl_leftUnitorHeadComparison_in_Theory3_of_triangleComparison
        K α q r hTri))

/-- Replacing the raw comparison `comp_in refl q` by the semantic left unitor
commutes with both the outer left whisker by `α` and the right whisker by the
tail path `r`. This isolates the bare-interface middle bridge between the
source-side `right` filler and the target-side `head` filler in the refl-tail
associator step. -/
noncomputable def reductionSeq_comp_associator_refl_rightHeadComparison_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let δ := reductionSeq_in_Theory1 K r
    let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    let head := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
    Theory3 K right head := by
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let lu := Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
  let δ := reductionSeq_in_Theory1 K r
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let head := Theory2.whiskerRight K (Theory2.whiskerLeft K α lu) δ
  have hη :
      Theory3 K η lu := by
    simpa [η, lu, reductionSeq_leftUnitor_in_Theory2] using
      (reductionSeq_comp_leftUnitor_direct_in_Theory3 K q)
  have hLeft :
      Theory3 K
        (Theory2.whiskerLeft K α η)
        (Theory2.whiskerLeft K α lu) := by
    exact Theory3.whiskerLeftCongr K α hη
  simpa [right, head] using
    (Theory3.whiskerRightCongr K hLeft δ)

/-- The smaller nested-whisker comparison
`assoc ; whiskerLeft (whiskerRight η δ) ; symm assoc ~ right`
already implies the target-side left-unitor head comparison, once the raw
`comp_in refl q` filler is replaced by the semantic left unitor using the bare
right-whisker congruence bridge above. -/
noncomputable def
    reductionSeq_comp_associator_refl_leftUnitorHeadComparison_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let luRight := Theory2.whiskerRight K
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ
    let head := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K α β δ)
        (Theory2.whiskerLeft K α luRight))
      (Theory2.trans K head
        (Theory2.associator K α γ δ)) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let Aγ := Theory2.associator K α γ δ
  let middle := Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ)
  let luRight := Theory2.whiskerRight K
    (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) δ
  let luMiddle := Theory2.whiskerLeft K α luRight
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let head := Theory2.whiskerRight K
    (Theory2.whiskerLeft K α
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
  have hWhisk :
      Theory3 K middle luMiddle := by
    have hInner :
        Theory3 K
          (Theory2.whiskerRight K η δ)
          luRight := by
      have hη :
          Theory3 K η
            (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)) := by
        simpa [η, reductionSeq_leftUnitor_in_Theory2] using
          (reductionSeq_comp_leftUnitor_direct_in_Theory3 K q)
      exact Theory3.whiskerRightCongr K hη δ
    exact Theory3.whiskerLeftCongr K α hInner
  have hRight :
      Theory3 K right head := by
    simpa [η, δ, right, head] using
      (reductionSeq_comp_associator_refl_rightHeadComparison_in_Theory3 K α q r)
  have hShell0 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K Aβ luMiddle)
          (Theory2.symm K Aγ))
        right := by
    exact Theory3.trans K
      (Theory3.transAssoc K Aβ luMiddle (Theory2.symm K Aγ))
      (Theory3.trans K
        (Theory3.transCongrRight K Aβ
          (Theory3.transCongrLeft K (Theory3.symm K hWhisk) (Theory2.symm K Aγ)))
        hNested)
  have hShell :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K Aβ luMiddle)
          (Theory2.symm K Aγ))
        head := by
    exact Theory3.trans K hShell0 hRight
  have hHeadExpand :
      Theory3 K
        head
        (Theory2.trans K
          (Theory2.trans K head Aγ)
          (Theory2.symm K Aγ)) := by
    exact Theory3.symm K <| Theory3.trans K
      (Theory3.transAssoc K head Aγ (Theory2.symm K Aγ))
      (Theory3.trans K
        (Theory3.transCongrRight K head
          (Theory3.transRightCancel K Aγ))
        (Theory3.transReflRight K head))
  exact Theory3.transRightCancelCongr K (Theory2.symm K Aγ) <|
    Theory3.trans K hShell hHeadExpand

/-- The whole refl/target split also follows from the smaller nested-whisker
comparison alone; the additional left-unitor triangle hypothesis is no longer
needed once the bare right/head bridge is available. -/
noncomputable def
    reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let head := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.trans K Aβ
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
              (Theory2.trans K e
                (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
      (Theory2.trans K head T) := by
  simpa using
    (reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_leftUnitorHeadComparison
      K α q r
      (reductionSeq_comp_associator_refl_leftUnitorHeadComparison_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested))

/-- The raw refl target leg can be rewritten as the comparison shell
`symm Aβ ; head ; T` already from the smaller nested-whisker comparison. This is
the exact right-half shell needed to compose with the source-side split via
`comparisonShellCompose_in_Theory3`. -/
noncomputable def
    reductionSeq_comp_associator_refl_targetHeadShell_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let head := Theory2.whiskerRight K
      (Theory2.whiskerLeft K α
        (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.whiskerLeft K α
        (Theory2.trans K
          (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
            (Theory2.trans K e
              (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r))))))
      (Theory2.trans K (Theory2.symm K Aβ)
        (Theory2.trans K head T)) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let target := Theory2.whiskerLeft K α
    (Theory2.trans K
      (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
        (Theory2.trans K e
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
  let head := Theory2.whiskerRight K
    (Theory2.whiskerLeft K α
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
  let T := Theory2.trans K
    (Theory2.associator K α γ δ)
    (Theory2.whiskerLeft K α c₀)
  have hTarget :
      Theory3 K
        (Theory2.trans K Aβ target)
        (Theory2.trans K head T) := by
    simpa [β, γ, δ, Aβ, c₀, e, head, T, target] using
      (reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested)
  have hExpand :
      Theory3 K
        (Theory2.trans K Aβ
          (Theory2.trans K (Theory2.symm K Aβ)
            (Theory2.trans K head T)))
        (Theory2.trans K head T) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transAssoc K Aβ (Theory2.symm K Aβ)
          (Theory2.trans K head T)))
      (Theory3.trans K
        (Theory3.transCongrLeft K
          (Theory3.transRightCancel K Aβ)
          (Theory2.trans K head T))
        (Theory3.transReflLeft K (Theory2.trans K head T)))
  exact Theory3.transLeftCancelCongr K Aβ <|
    Theory3.trans K hTarget (Theory3.symm K hExpand)

/-- The refl target-side shell can also be packaged directly with the raw
right-whiskered comparison filler, not just the semantic left-unitor head.
This matches the source-side split from
`reductionSeq_comp_associator_refl_sourceWhiskerSplit_in_Theory3_of_nestedWhiskerComparison`
without needing an extra intermediate rewrite. -/
noncomputable def
    reductionSeq_comp_associator_refl_targetRightShell_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let Aβ := Theory2.associator K α β δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.trans K Aβ
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
              (Theory2.trans K e
                (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
      (Theory2.trans K right T) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let Aβ := Theory2.associator K α β δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let head := Theory2.whiskerRight K
    (Theory2.whiskerLeft K α
      (Theory2.leftUnitor K (reductionSeq_in_Theory1 K q))) δ
  let T := Theory2.trans K
    (Theory2.associator K α γ δ)
    (Theory2.whiskerLeft K α c₀)
  have hHeadShell :
      Theory3 K
        (Theory2.trans K Aβ
          (Theory2.whiskerLeft K α
            (Theory2.trans K
              (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
              (Theory2.trans K
                (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
                (Theory2.trans K e
                  (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))))
        (Theory2.trans K head T) := by
    simpa [β, γ, δ, Aβ, c₀, e, head, T] using
      (reductionSeq_comp_associator_refl_targetWhiskerSplit_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested)
  exact Theory3.trans K hHeadShell
    (Theory3.transCongrLeft K
      (Theory3.symm K
        (reductionSeq_comp_associator_refl_rightHeadComparison_in_Theory3 K α q r))
      T)

/-- Splicing the source-side split directly to the matching raw right-half
target leg yields the explicit loop
`symm T ; symm right ; right ; T`. Unlike
`reductionSeq_comp_associator_refl_theoryWhiskerLeft_in_Theory3`, this keeps the
split composite visible, which is the exact form needed when comparing other
refl-specialized shells against the same loop. -/
noncomputable def
    reductionSeq_comp_associator_refl_splitLoop_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
    let δ := reductionSeq_in_Theory1 K r
    let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let T := Theory2.trans K
      (Theory2.associator K α γ δ)
      (Theory2.whiskerLeft K α c₀)
    let target := Theory2.whiskerLeft K α
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
        target)
      (Theory2.trans K (Theory2.symm K T)
        (Theory2.trans K (Theory2.symm K right)
          (Theory2.trans K right T))) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let T := Theory2.trans K
    (Theory2.associator K α γ δ)
    (Theory2.whiskerLeft K α c₀)
  let sourceShell := Theory2.trans K
    (Theory2.symm K T)
    (Theory2.trans K (Theory2.symm K right) Aβ)
  let target := Theory2.whiskerLeft K α
    (Theory2.trans K
      (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
        (Theory2.trans K e
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
  have hSource :
      Theory3 K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
        sourceShell := by
    simpa [β, η, γ, δ, Aβ, right, c₀, T, sourceShell] using
      (reductionSeq_comp_associator_refl_sourceWhiskerSplit_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested)
  have hTarget :
      Theory3 K
        (Theory2.trans K Aβ target)
        (Theory2.trans K right T) := by
    simpa [β, η, γ, δ, Aβ, right, c₀, e, T, target] using
      (reductionSeq_comp_associator_refl_targetRightShell_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested)
  have h0 :
      Theory3 K
        (Theory2.trans K
          (Theory2.whiskerLeft K α
            (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
          target)
        (Theory2.trans K sourceShell target) := by
    exact Theory3.transCongrLeft K hSource target
  have h1 :
      Theory3 K
        (Theory2.trans K sourceShell target)
        (Theory2.trans K
          (Theory2.symm K T)
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K right) Aβ)
            target)) := by
    exact Theory3.transAssoc K
      (Theory2.symm K T)
      (Theory2.trans K (Theory2.symm K right) Aβ)
      target
  have h2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K T)
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K right) Aβ)
            target))
        (Theory2.trans K
          (Theory2.symm K T)
          (Theory2.trans K
            (Theory2.symm K right)
            (Theory2.trans K Aβ target))) := by
    exact Theory3.transCongrRight K
      (Theory2.symm K T)
      (Theory3.transAssoc K (Theory2.symm K right) Aβ target)
  have h3 :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K T)
          (Theory2.trans K
            (Theory2.symm K right)
            (Theory2.trans K Aβ target)))
        (Theory2.trans K
          (Theory2.symm K T)
          (Theory2.trans K
            (Theory2.symm K right)
            (Theory2.trans K right T))) := by
    exact Theory3.transCongrRight K
      (Theory2.symm K T)
      (Theory3.transCongrRight K (Theory2.symm K right) hTarget)
  exact Theory3.trans K h0
    (Theory3.trans K h1
      (Theory3.trans K h2 h3))

/-- The canonical loop shape `symm T ; symm right ; right ; T` contracts by pure
associativity and cancellation. This is the final algebraic step behind the
refl-specialized split-loop frontier. -/
private noncomputable def Theory3.transSymmDoubleLoopCancel
    (K : ExtensionalKanComplex) {L M : Term}
    {α β γ : Theory1 K L M}
    (T : Theory2 K α β) (right : Theory2 K γ α) :
    Theory3 K
      (Theory2.trans K (Theory2.symm K T)
        (Theory2.trans K (Theory2.symm K right)
          (Theory2.trans K right T)))
      (Theory2.refl K β) := by
  have hInner0 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K right)
          (Theory2.trans K right T))
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K right) right)
          T) := by
    exact Theory3.symm K (Theory3.transAssoc K (Theory2.symm K right) right T)
  have hInner1 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K right) right)
          T)
        (Theory2.trans K (Theory2.refl K α) T) := by
    exact Theory3.transCongrLeft K (Theory3.transLeftCancel K right) T
  have hInner2 :
      Theory3 K
        (Theory2.trans K (Theory2.refl K α) T)
        T := by
    exact Theory3.transReflLeft K T
  have hInner :
      Theory3 K
        (Theory2.trans K (Theory2.symm K right)
          (Theory2.trans K right T))
        T := by
    exact Theory3.trans K hInner0 (Theory3.trans K hInner1 hInner2)
  exact Theory3.trans K
    (Theory3.transCongrRight K (Theory2.symm K T) hInner)
    (Theory3.transLeftCancel K T)

/-- After splicing the refl source and target halves, the remaining explicit loop
already contracts on the bare interface without any additional coherence
axioms. -/
noncomputable def
    reductionSeq_comp_associator_refl_splitLoopContract_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let δ := reductionSeq_in_Theory1 K r
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let target := Theory2.whiskerLeft K α
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
        target)
      (Theory2.refl K
        (Theory1.comp K α
          (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))) := by
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K r
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let T := Theory2.trans K
    (Theory2.associator K α γ δ)
    (Theory2.whiskerLeft K α c₀)
  let target := Theory2.whiskerLeft K α
    (Theory2.trans K
      (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
        (Theory2.trans K e
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
  exact Theory3.trans K
    (reductionSeq_comp_associator_refl_splitLoop_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)
    (by
      simpa [η, γ, δ, right, c₀, e, T] using
        (Theory3.transSymmDoubleLoopCancel K T right))

/-- The normalized refl split loop compares directly with the semantic left
whisker of the base refl associator shell. Both are loops at the same
right-associated endpoint, and both now contract on the bare interface. -/
noncomputable def
    reductionSeq_comp_associator_refl_splitLoop_to_theoryWhiskerLeft_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let δ := reductionSeq_in_Theory1 K r
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let target := Theory2.whiskerLeft K α
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r))
        target)
      (Theory2.whiskerLeft K α
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r)) := by
  have hWhisk :
      Theory3 K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
        (Theory2.refl K
          (Theory1.comp K α
            (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))) := by
    let hEq :
        congrArg (fun δ => Theory1.comp K α δ)
          (congrArg (fun t => reductionSeq_in_Theory1 K t)
            (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)) = rfl := by
      exact Subsingleton.elim _ _
    exact Theory3.trans K
      (Theory3.whiskerLeftCongrOfEq K α
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r))
        (reductionSeq_comp_associator_refl_in_Theory3 K q r))
      (Theory3.ofEq K (by
        cases hEq
        rfl))
  exact Theory3.trans K
    (reductionSeq_comp_associator_refl_splitLoopContract_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)
    (Theory3.symm K hWhisk)

/-- Canceling the common source-side whisker from the split-loop comparison
isolates the normalized target leg against the semantic middle-and-target tail
of the whiskered reflexive associator shell. -/
noncomputable def
    reductionSeq_comp_associator_refl_target_to_theoryWhiskerTail_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let δ := reductionSeq_in_Theory1 K r
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
    let target := Theory2.whiskerLeft K α
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
          (Theory2.trans K e
            (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
    Theory3 K
      target
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r))
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r))) := by
  let source := Theory2.whiskerLeft K α
    (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r)
  let middle := Theory2.whiskerLeft K α
    (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
  let tail := Theory2.whiskerLeft K α
    (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r)
  let shell := Theory2.whiskerLeft K α
    (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r)
  let δ := reductionSeq_in_Theory1 K r
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let target := Theory2.whiskerLeft K α
    (Theory2.trans K
      (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
        (Theory2.trans K e
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
  have hWhiskExpand0 :
      Theory3 K shell
        (Theory2.trans K source
          (Theory2.whiskerLeft K α
            (Theory2.trans K
              (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
              (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r)))) := by
    simpa [shell, source, reductionSeq_associator_shell_in_Theory2] using
      (Theory3.whiskerLeftTrans K α
        (reductionSeq_associator_source_in_Theory2 K (ReductionSeq.refl M) q r)
        (Theory2.trans K
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r)))
  have hWhiskExpand1 :
      Theory3 K
        (Theory2.whiskerLeft K α
          (Theory2.trans K
            (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
            (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r)))
        (Theory2.trans K middle tail) := by
    simpa [middle, tail] using
      (Theory3.whiskerLeftTrans K α
        (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r)
        (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r))
  have hWhiskExpand :
      Theory3 K shell
        (Theory2.trans K source (Theory2.trans K middle tail)) := by
    exact Theory3.trans K hWhiskExpand0
      (Theory3.transCongrRight K source hWhiskExpand1)
  have hCompare :
      Theory3 K
        (Theory2.trans K source target)
        (Theory2.trans K source (Theory2.trans K middle tail)) := by
    exact Theory3.trans K
      (reductionSeq_comp_associator_refl_splitLoop_to_theoryWhiskerLeft_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested)
      hWhiskExpand
  exact Theory3.transLeftCancelCongr K source hCompare

/-- The normalized right-hand refl shell can now be read directly as the
semantic whiskered tail `whiskerLeft α assocRest ; whiskerLeft α targetRest`,
without routing through the semantic left-unitor head. -/
noncomputable def
    reductionSeq_comp_associator_refl_rightShell_to_theoryWhiskerTail_in_Theory3_of_nestedWhiskerComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
      let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K r
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K α β δ)
          (Theory2.trans K
            (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
            (Theory2.symm K (Theory2.associator K α γ δ))))
        (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)) :
    let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
    let δ := reductionSeq_in_Theory1 K r
    let Aβ := Theory2.associator K α β δ
    let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
    let c₀ := reductionSeq_comp_in_Theory2 K
      (ReductionSeq.concat (ReductionSeq.refl M) q) r
    let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
    let T := Theory2.trans K
      (Theory2.associator K α
        (reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)) δ)
      (Theory2.whiskerLeft K α c₀)
    Theory3 K
      (Theory2.trans K (Theory2.symm K Aβ)
        (Theory2.trans K right T))
      (Theory2.trans K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_in_Theory2 K (ReductionSeq.refl M) q r))
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_target_in_Theory2 K (ReductionSeq.refl M) q r))) := by
  let β := Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K q)
  let δ := reductionSeq_in_Theory1 K r
  let Aβ := Theory2.associator K α β δ
  let η := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) q
  let c₀ := reductionSeq_comp_in_Theory2 K
    (ReductionSeq.concat (ReductionSeq.refl M) q) r
  let e := reductionSeq_comp_in_Theory2 K (ReductionSeq.refl M) (ReductionSeq.concat q r)
  let right := Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ
  let target := Theory2.whiskerLeft K α
    (Theory2.trans K
      (Theory2.associator K (Theory1.refl K M) (reductionSeq_in_Theory1 K q) δ)
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K M) c₀)
        (Theory2.trans K e
          (reductionSeq_leftUnitor_shell_in_Theory2 K (ReductionSeq.concat q r)))))
  let T := Theory2.trans K
    (Theory2.associator K α
      (reductionSeq_in_Theory1 K (ReductionSeq.concat (ReductionSeq.refl M) q)) δ)
    (Theory2.whiskerLeft K α c₀)
  have hRightShell :
      Theory3 K
        (Theory2.trans K Aβ target)
        (Theory2.trans K right T) := by
    simpa [β, δ, Aβ, η, c₀, e, right, T, target] using
      (reductionSeq_comp_associator_refl_targetRightShell_in_Theory3_of_nestedWhiskerComparison
        K α q r hNested)
  have hExpand :
      Theory3 K
        target
        (Theory2.trans K (Theory2.symm K Aβ)
          (Theory2.trans K right T)) := by
    have hExpand0 :
        Theory3 K
          (Theory2.trans K Aβ
            (Theory2.trans K (Theory2.symm K Aβ)
              (Theory2.trans K right T)))
          (Theory2.trans K right T) := by
      exact Theory3.trans K
        (Theory3.symm K
          (Theory3.transAssoc K Aβ (Theory2.symm K Aβ)
            (Theory2.trans K right T)))
        (Theory3.trans K
          (Theory3.transCongrLeft K
            (Theory3.transRightCancel K Aβ)
            (Theory2.trans K right T))
          (Theory3.transReflLeft K (Theory2.trans K right T)))
    exact Theory3.transLeftCancelCongr K Aβ <|
      Theory3.trans K hRightShell (Theory3.symm K hExpand0)
  exact Theory3.trans K (Theory3.symm K hExpand)
    (reductionSeq_comp_associator_refl_target_to_theoryWhiskerTail_in_Theory3_of_nestedWhiskerComparison
      K α q r hNested)

/-- Refl-specialized inverse base theorem: a reduced WLWR right-half comparison
on a single leading inverse step already yields the full associator shell
comparison for that one-step path. -/
noncomputable def reductionSeq_comp_associator_stepInv_refl_in_Theory3_of_rightComparison
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep M L) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hRight :
      let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ)))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K0 r
  have hMidFront :
      let γ := reductionSeq_in_Theory1 K0
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ)) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonFromTriangleComparison
        K0 α η δ hRight)
  have hTri :
      let β := Theory1.comp K0
        (reductionSeq_in_Theory1 K0 (ReductionSeq.refl M))
        (reductionSeq_in_Theory1 K0 q)
      let γ := reductionSeq_in_Theory1 K0
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.transPath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K0.toReflexiveKanComplex.toKanComplex.symmPath2
              (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) := by
    simpa using
      (reductionSeq_comp_triangle_target_stepInv_in_Theory3 K0 s
        (ReductionSeq.refl M) q r hMidFront)
  have hHead :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0
          (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r)
        (Theory2.whiskerLeft K0
          (betaEtaStepInv_in_Theory1 K0 L M s)
          (reductionSeq_associator_shell_in_Theory2 K0
            (ReductionSeq.refl M) q r)) :=
    reductionSeq_comp_associator_stepInvHead_from_triangle_in_Theory3 K s
      (ReductionSeq.refl M) q r hTri
  exact reductionSeq_comp_associator_stepInv_finish_in_Theory3 K0 s
    (ReductionSeq.refl M) q r
    (reductionSeq_comp_associator_refl_in_Theory3 K0 q r)
    hHead

/-- Refl-specialized inverse base theorem, wired from the normalized frontier
`mid ; symm assoc ~ right`. -/
noncomputable def reductionSeq_comp_associator_stepInv_refl_in_Theory3_of_normalizedRightComparison
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep M L) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNorm :
      let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ) (η ρ))
            (δ ρ))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K0 r
  have hRight :
      let γ := reductionSeq_in_Theory1 K0
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.symmPath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
        K0 α η δ hNorm)
  exact reductionSeq_comp_associator_stepInv_refl_in_Theory3_of_rightComparison
    K s q r hRight

/-- Refl-specialized inverse base theorem, wired from the smaller nested-whisker
comparison
`assoc ; whiskerLeft (whiskerRight leftUnitor δ) ; symm assoc ~ right`. -/
noncomputable def reductionSeq_comp_associator_stepInv_refl_in_Theory3_of_nestedWhiskerComparison
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep M L) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
      let β := Theory1.comp K.toExtensionalKanComplex
        (Theory1.refl K.toExtensionalKanComplex M)
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.associator K.toExtensionalKanComplex α β δ)
          (Theory2.trans K.toExtensionalKanComplex
            (Theory2.whiskerLeft K.toExtensionalKanComplex α
              (Theory2.whiskerRight K.toExtensionalKanComplex η δ))
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex α γ δ))))
        (Theory2.whiskerRight K.toExtensionalKanComplex
          (Theory2.whiskerLeft K.toExtensionalKanComplex α η) δ)) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let β := Theory1.comp K0 (Theory1.refl K0 M) (reductionSeq_in_Theory1 K0 q)
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K0 r
  have hNorm :
      Theory3 K0
        (Theory2.trans K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.symm K0 (Theory2.associator K0 α γ δ)))
        (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α η) δ) := by
    simpa [α, β, η, γ, δ] using
      (reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
        K0 α η δ hNested)
  exact reductionSeq_comp_associator_stepInv_refl_in_Theory3_of_normalizedRightComparison
    K s q r hNorm

/-- Forward-step wrapper around the generic source/triangle/right-comparison slice:
once the reduced right-half comparison is known for an arbitrary tail `rest` and
the tail associator shell itself is already normalized, the full step case
follows by the existing head-bridge and bookkeeping lemmas. -/
noncomputable def reductionSeq_comp_associator_step_in_Theory3_of_rightComparison
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hRight :
      let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ))))
    (ih :
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc rest q r)))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s rest) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 rest q
  let δ := reductionSeq_in_Theory1 K0 r
  have hMidFront :
      let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ)) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonFromTriangleComparison
        K0 α η δ hRight)
  have hTri :
      let β := Theory1.comp K0
        (reductionSeq_in_Theory1 K0 rest)
        (reductionSeq_in_Theory1 K0 q)
      let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.transPath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K0.toReflexiveKanComplex.toKanComplex.symmPath2
              (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) := by
    simpa using
      (reductionSeq_comp_triangle_target_step_in_Theory3 K0 s rest q r hMidFront)
  have hHead :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0
          (ReductionSeq.step s rest) q r)
        (Theory2.whiskerLeft K0
          (betaEtaStep_in_Theory1 K0 L M s)
          (reductionSeq_associator_shell_in_Theory2 K0 rest q r)) :=
    reductionSeq_comp_associator_stepHead_from_triangle_in_Theory3 K s
      rest q r hTri
  exact reductionSeq_comp_associator_step_finish_in_Theory3 K0 s
    rest q r ih hHead

/-- Forward-step wrapper wired from the normalized frontier
`mid ; symm assoc ~ right` for an arbitrary tail `rest`. -/
noncomputable def reductionSeq_comp_associator_step_in_Theory3_of_normalizedRightComparison
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hNorm :
      let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ) (η ρ))
            (δ ρ)))
    (ih :
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc rest q r)))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s rest) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 rest q
  let δ := reductionSeq_in_Theory1 K0 r
  have hRight :
      let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.symmPath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
        K0 α η δ hNorm)
  exact reductionSeq_comp_associator_step_in_Theory3_of_rightComparison
    K s rest q r hRight ih

/-- Inverse-step analogue of
`reductionSeq_comp_associator_step_in_Theory3_of_rightComparison`. -/
noncomputable def reductionSeq_comp_associator_stepInv_in_Theory3_of_rightComparison
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hRight :
      let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ))))
    (ih :
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc rest q r)))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s rest) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 rest q
  let δ := reductionSeq_in_Theory1 K0 r
  have hMidFront :
      let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ)) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonFromTriangleComparison
        K0 α η δ hRight)
  have hTri :
      let β := Theory1.comp K0
        (reductionSeq_in_Theory1 K0 rest)
        (reductionSeq_in_Theory1 K0 q)
      let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.transPath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K0.toReflexiveKanComplex.toKanComplex.symmPath2
              (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) := by
    simpa using
      (reductionSeq_comp_triangle_target_stepInv_in_Theory3 K0 s rest q r hMidFront)
  have hHead :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0
          (ReductionSeq.stepInv s rest) q r)
        (Theory2.whiskerLeft K0
          (betaEtaStepInv_in_Theory1 K0 L M s)
          (reductionSeq_associator_shell_in_Theory2 K0 rest q r)) :=
    reductionSeq_comp_associator_stepInvHead_from_triangle_in_Theory3 K s
      rest q r hTri
  exact reductionSeq_comp_associator_stepInv_finish_in_Theory3 K0 s
    rest q r ih hHead

/-- Inverse-step wrapper wired from the normalized frontier
`mid ; symm assoc ~ right` for an arbitrary tail `rest`. -/
noncomputable def reductionSeq_comp_associator_stepInv_in_Theory3_of_normalizedRightComparison
    (K : CoherentExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (hNorm :
      let α := betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex rest q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat rest q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ) (η ρ))
            (δ ρ)))
    (ih :
      Theory3 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)
        (Theory2.ofEq K.toExtensionalKanComplex
          (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
            (ReductionSeq.concat_assoc rest q r)))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s rest) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 rest q
  let δ := reductionSeq_in_Theory1 K0 r
  have hRight :
      let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.symmPath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
        K0 α η δ hNorm)
  exact reductionSeq_comp_associator_stepInv_in_Theory3_of_rightComparison
    K s rest q r hRight ih

/-- The interpreted syntactic left unitor agrees with the structural-endpoint
left-unitor shell built from the normalized semantic left unitor. -/
noncomputable def homotopy2_leftUnitor_bridge_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (HigherTerms.leftUnitor p))
      (reductionSeq_leftUnitor_shell_in_Theory2 K p) :=
  Theory3.symm K <| by
    change Theory3 K
      (reductionSeq_leftUnitor_shell_in_Theory2 K p)
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (ReductionSeq.concat_refl_left p)))
    simpa [reductionSeq_leftUnitor_shell_in_Theory2, reductionSeq_leftUnitor_in_Theory2,
      reductionSeq_comp_in_Theory2, Theory2.ofEq] using
      (Theory3.transLeftCancel K (reductionSeq_leftUnitor_in_Theory2 K p))

/-- Left whiskering preserves the left-unitor endpoint bridge. This is the
structural form needed for the source side of the syntactic triangle
constructor. -/
noncomputable def homotopy2_whiskerLeft_leftUnitor_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) (p : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (HigherTerms.whiskerLeft r (HigherTerms.leftUnitor p)))
      (reductionSeq_whiskerLeft_in_Theory2 K r
        (reductionSeq_leftUnitor_shell_in_Theory2 K p)) := by
  change Theory3 K
    (reductionSeq_whiskerLeft_in_Theory2 K r
      (homotopy2_in_Theory2 K (HigherTerms.leftUnitor p)))
    (reductionSeq_whiskerLeft_in_Theory2 K r
      (reductionSeq_leftUnitor_shell_in_Theory2 K p))
  exact reductionSeq_whiskerLeftCongr_in_Theory3 K r
    (homotopy2_leftUnitor_bridge_in_Theory3 K p)

/-- Degenerating the semantic composition triangle yields a boundary-aware
semantic tetrahedron whose middle face is the reflexive 2-cell on the semantic
composite path. -/
noncomputable def reductionSeq_comp_refl_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K q)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)) :=
  TheoryTriangle.reflTetrahedron K
    (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))

/-- The interpreted structural associator carries an explicit semantic
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_associator_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    TheoryTetrahedron K
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))))
      (Theory2.toTriangle K (reductionSeq_associator_in_Theory2 K p q r))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p)
        (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)))
      (Theory1.assocTriangle K (reductionSeq_in_Theory1 K p)
        (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)) :=
  Theory3.associatorTetrahedron K
    (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)

/-- The interpreted structural left unitor carries an explicit semantic
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_leftUnitor_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K p)))
      (Theory2.toTriangle K (reductionSeq_leftUnitor_in_Theory2 K p))
      (Theory1.sourceDegenerateTriangle K (reductionSeq_in_Theory1 K p))
      (Theory1.compTriangle K (Theory1.refl K M) (reductionSeq_in_Theory1 K p)) :=
  Theory3.leftUnitorTetrahedron K (reductionSeq_in_Theory1 K p)

/-- The interpreted structural right unitor carries an explicit semantic
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_rightUnitor_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K (reductionSeq_rightUnitor_in_Theory2 K p))
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K p)))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (Theory1.refl K N)) :=
  Theory3.rightUnitorTetrahedron K (reductionSeq_in_Theory1 K p)

/-- The interpreted structural vertical composition carries an explicit
semantic tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_trans_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {M N : Term}
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K (homotopy2_in_Theory2 K β))
      (Theory2.toTriangle K (homotopy2_in_Theory2 K (Homotopy2.trans α β)))
      (Theory2.toTriangle K (homotopy2_in_Theory2 K α)) :=
  Theory3.transFillerTetrahedron K
    (homotopy2_in_Theory2 K α)
    (homotopy2_in_Theory2 K β)

/-- Left whiskering of an interpreted explicit 2-cell carries an explicit
semantic tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerLeft_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (homotopy2_in_Theory2 K α))
      (Theory2.toTriangle K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K q))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K p)) :=
  Theory3.whiskerLeftTetrahedron K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)

/-- Left whiskering commutes with vertical composition for interpreted explicit
2-cells. -/
noncomputable def homotopy2_whiskerLeftTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q s : ReductionSeq M N}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    Theory3 K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.trans K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)))
      (Theory2.trans K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α))
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K β))) :=
  Theory3.whiskerLeftTrans K (reductionSeq_in_Theory1 K r)
    (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)

/-- Left whiskering along a composite explicit path agrees with iterated left
whiskering plus the associator comparison on interpreted explicit 2-cells. -/
noncomputable def homotopy2_whiskerLeftComp_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    {r s : ReductionSeq N P} (α : Homotopy2 r s) :
    Theory3 K
      (Theory2.whiskerLeft K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
        (homotopy2_in_Theory2 K α))
      (Theory2.trans K
        (Theory2.associator K
          (reductionSeq_in_Theory1 K p)
          (reductionSeq_in_Theory1 K q)
          (reductionSeq_in_Theory1 K r))
        (Theory2.trans K
          (Theory2.whiskerLeft K
            (reductionSeq_in_Theory1 K p)
            (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K q)
              (homotopy2_in_Theory2 K α)))
          (Theory2.symm K
            (Theory2.associator K
              (reductionSeq_in_Theory1 K p)
              (reductionSeq_in_Theory1 K q)
              (reductionSeq_in_Theory1 K s))))) :=
  Theory3.whiskerLeftComp K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)
    (homotopy2_in_Theory2 K α)

/-- Composing two comparison shells with a shared middle comparison contracts to
the comparison shell of the semantic composite. -/
noncomputable def comparisonShellCompose_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {αs αs' αm αm' αt αt' : Theory1 K M N}
    (cₛ : Theory2 K αs αs') (η : Theory2 K αs αm)
    (cₘ : Theory2 K αm αm') (θ : Theory2 K αm αt)
    (cₜ : Theory2 K αt αt') :
    Theory3 K
      (Theory2.trans K
        (Theory2.trans K (Theory2.symm K cₛ) (Theory2.trans K η cₘ))
        (Theory2.trans K (Theory2.symm K cₘ) (Theory2.trans K θ cₜ)))
      (Theory2.trans K (Theory2.symm K cₛ)
        (Theory2.trans K (Theory2.trans K η θ) cₜ)) := by
  have hInner :
      Theory3 K
        (Theory2.trans K (Theory2.trans K η cₘ)
          (Theory2.trans K (Theory2.symm K cₘ) (Theory2.trans K θ cₜ)))
        (Theory2.trans K (Theory2.trans K η θ) cₜ) := by
    exact Theory3.trans K
      (Theory3.transAssoc K η cₘ
        (Theory2.trans K (Theory2.symm K cₘ) (Theory2.trans K θ cₜ)))
      (Theory3.trans K
        (Theory3.transCongrRight K η
          (Theory3.trans K
            (Theory3.symm K
              (Theory3.transAssoc K cₘ (Theory2.symm K cₘ)
                (Theory2.trans K θ cₜ)))
            (Theory3.trans K
              (Theory3.transCongrLeft K
                (Theory3.transRightCancel K cₘ)
                (Theory2.trans K θ cₜ))
              (Theory3.transReflLeft K (Theory2.trans K θ cₜ)))))
        (Theory3.symm K (Theory3.transAssoc K η θ cₜ)))
  exact Theory3.trans K
    (Theory3.transAssoc K (Theory2.symm K cₛ) (Theory2.trans K η cₘ)
      (Theory2.trans K (Theory2.symm K cₘ) (Theory2.trans K θ cₜ)))
    (Theory3.transCongrRight K (Theory2.symm K cₛ) hInner)

/-- Inverse shell form of `Theory3.whiskerLeftComp`. -/
noncomputable def Theory3.whiskerLeftCompShell
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) {γ δ : Theory1 K N P}
    (η : Theory2 K γ δ) :
    Theory3 K
      (Theory2.trans K
        (Theory2.symm K (Theory2.associator K α β γ))
        (Theory2.trans K
          (Theory2.whiskerLeft K (Theory1.comp K α β) η)
          (Theory2.associator K α β δ)))
      (Theory2.whiskerLeft K α (Theory2.whiskerLeft K β η)) := by
  let Aγ := Theory2.associator K α β γ
  let Aδ := Theory2.associator K α β δ
  let W := Theory2.whiskerLeft K (Theory1.comp K α β) η
  let nested := Theory2.whiskerLeft K α (Theory2.whiskerLeft K β η)
  have hComp :
      Theory3 K
        W
        (Theory2.trans K Aγ
          (Theory2.trans K nested (Theory2.symm K Aδ))) :=
    Theory3.whiskerLeftComp K α β η
  have h0 :
      Theory3 K
        (Theory2.trans K (Theory2.symm K Aγ) (Theory2.trans K W Aδ))
        (Theory2.trans K (Theory2.trans K (Theory2.symm K Aγ) W) Aδ) := by
    exact Theory3.symm K (Theory3.transAssoc K (Theory2.symm K Aγ) W Aδ)
  have h1 :
      Theory3 K
        (Theory2.trans K (Theory2.trans K (Theory2.symm K Aγ) W) Aδ)
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K Aγ)
            (Theory2.trans K Aγ
              (Theory2.trans K nested (Theory2.symm K Aδ))))
          Aδ) := by
    exact Theory3.transCongrLeft K
      (Theory3.transCongrRight K (Theory2.symm K Aγ) hComp)
      Aδ
  have h2 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K Aγ)
            (Theory2.trans K Aγ
              (Theory2.trans K nested (Theory2.symm K Aδ))))
          Aδ)
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K Aγ) Aγ)
            (Theory2.trans K nested (Theory2.symm K Aδ)))
          Aδ) := by
    exact Theory3.transCongrLeft K
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K Aγ) Aγ
          (Theory2.trans K nested (Theory2.symm K Aδ))))
      Aδ
  have h3 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K Aγ) Aγ)
            (Theory2.trans K nested (Theory2.symm K Aδ)))
          Aδ)
        (Theory2.trans K
          (Theory2.trans K (Theory2.refl K _) (Theory2.trans K nested (Theory2.symm K Aδ)))
          Aδ) := by
    exact Theory3.transCongrLeft K
      (Theory3.transCongrLeft K (Theory3.transLeftCancel K Aγ)
        (Theory2.trans K nested (Theory2.symm K Aδ)))
      Aδ
  have h4 :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.refl K _) (Theory2.trans K nested (Theory2.symm K Aδ)))
          Aδ)
        (Theory2.trans K (Theory2.trans K nested (Theory2.symm K Aδ)) Aδ) := by
    exact Theory3.transCongrLeft K
      (Theory3.transReflLeft K (Theory2.trans K nested (Theory2.symm K Aδ)))
      Aδ
  have h5 :
      Theory3 K
        (Theory2.trans K (Theory2.trans K nested (Theory2.symm K Aδ)) Aδ)
        (Theory2.trans K nested (Theory2.trans K (Theory2.symm K Aδ) Aδ)) := by
    exact Theory3.transAssoc K nested (Theory2.symm K Aδ) Aδ
  have h6 :
      Theory3 K
        (Theory2.trans K nested (Theory2.trans K (Theory2.symm K Aδ) Aδ))
        (Theory2.trans K nested (Theory2.refl K _)) := by
    exact Theory3.transCongrRight K nested (Theory3.transLeftCancel K Aδ)
  have h7 :
      Theory3 K
        (Theory2.trans K nested (Theory2.refl K _))
        nested := by
    exact Theory3.transReflRight K nested
  exact Theory3.trans K h0
    (Theory3.trans K h1
      (Theory3.trans K h2
        (Theory3.trans K h3
          (Theory3.trans K h4 (Theory3.trans K h5 (Theory3.trans K h6 h7))))))

/-- Structural left whiskering along an explicit path is the comparison shell
built from semantic left whiskering and the explicit-composition bridges. -/
noncomputable def reductionSeq_whiskerLeft_shell_to_struct_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)) →
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K (reductionSeq_comp_in_Theory2 K r p))
          (Theory2.trans K
            (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) η)
            (reductionSeq_comp_in_Theory2 K r q)))
        (reductionSeq_whiskerLeft_in_Theory2 K r η)
  | _, _, _, .refl _, p, q, η => by
      have hNat :
          Theory3 K
            (Theory2.trans K
              (Theory2.whiskerLeft K (Theory1.refl K _) η)
              (Theory2.leftUnitor K _))
            (Theory2.trans K (Theory2.leftUnitor K _) η) :=
        Theory3.leftUnitorNaturality K η
      have h0 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.leftUnitor K _))
              (Theory2.trans K
                (Theory2.whiskerLeft K (Theory1.refl K _) η)
                (Theory2.leftUnitor K _)))
            (Theory2.trans K
              (Theory2.symm K (Theory2.leftUnitor K _))
              (Theory2.trans K (Theory2.leftUnitor K _) η)) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.leftUnitor K _)) hNat
      have h1 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.leftUnitor K _))
              (Theory2.trans K (Theory2.leftUnitor K _) η))
            η := by
        exact Theory3.trans K
          (Theory3.symm K
            (Theory3.transAssoc K
              (Theory2.symm K (Theory2.leftUnitor K _))
              (Theory2.leftUnitor K _) η))
          (Theory3.trans K
            (Theory3.transCongrLeft K
              (Theory3.transLeftCancel K (Theory2.leftUnitor K _)) η)
            (Theory3.transReflLeft K η))
      simpa [reductionSeq_comp_in_Theory2, reductionSeq_whiskerLeft_in_Theory2,
        reductionSeq_in_Theory1] using Theory3.trans K h0 h1
  | _, _, _, .step s rest, p, q, η => by
      let σ := betaEtaStep_in_Theory1 K _ _ s
      let ρ := reductionSeq_in_Theory1 K rest
      let cp := reductionSeq_comp_in_Theory2 K rest p
      let cq := reductionSeq_comp_in_Theory2 K rest q
      let Aₚ := Theory2.associator K σ ρ (reductionSeq_in_Theory1 K p)
      let A_q := Theory2.associator K σ ρ (reductionSeq_in_Theory1 K q)
      let leftRest := Theory2.whiskerLeft K ρ η
      let leftComp := Theory2.whiskerLeft K (Theory1.comp K σ ρ) η
      have h0 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (reductionSeq_comp_in_Theory2 K (.step s rest) p))
              (Theory2.trans K
                (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K (.step s rest)) η)
                (reductionSeq_comp_in_Theory2 K (.step s rest) q)))
            (Theory2.trans K
              (Theory2.trans K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
                (Theory2.symm K Aₚ))
              (Theory2.trans K leftComp
                (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))) := by
        exact Theory3.transCongrLeft K
          (by
            simpa [σ, ρ, cp, Aₚ, reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1]
              using Theory3.symmTrans K Aₚ (Theory2.whiskerLeft K σ cp))
          (Theory2.trans K leftComp
            (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))
      have h1 :
          Theory3 K
            (Theory2.trans K
              (Theory2.trans K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
                (Theory2.symm K Aₚ))
              (Theory2.trans K leftComp
                (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq))))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.symm K Aₚ)
                (Theory2.trans K leftComp
                  (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq))))) := by
        exact Theory3.transAssoc K
          (Theory2.symm K (Theory2.whiskerLeft K σ cp))
          (Theory2.symm K Aₚ)
          (Theory2.trans K leftComp
            (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))
      have h2Inner :
          Theory3 K
            (Theory2.trans K (Theory2.symm K Aₚ)
              (Theory2.trans K leftComp
                (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq))))
            (Theory2.trans K
              (Theory2.trans K (Theory2.symm K Aₚ)
                (Theory2.trans K leftComp A_q))
              (Theory2.whiskerLeft K σ cq)) := by
        exact Theory3.trans K
          (Theory3.transCongrRight K (Theory2.symm K Aₚ)
            (Theory3.symm K
              (Theory3.transAssoc K leftComp A_q
                (Theory2.whiskerLeft K σ cq))))
          (Theory3.symm K
            (Theory3.transAssoc K (Theory2.symm K Aₚ)
              (Theory2.trans K leftComp A_q)
              (Theory2.whiskerLeft K σ cq)))
      have h2 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.symm K Aₚ)
                (Theory2.trans K leftComp
                  (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K
                (Theory2.trans K (Theory2.symm K Aₚ)
                  (Theory2.trans K leftComp A_q))
                (Theory2.whiskerLeft K σ cq))) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.whiskerLeft K σ cp)) h2Inner
      have h3Inner :
          Theory3 K
            (Theory2.trans K (Theory2.symm K Aₚ)
              (Theory2.trans K leftComp A_q))
            (Theory2.whiskerLeft K σ leftRest) := by
        exact Theory3.whiskerLeftCompShell K σ ρ η
      have h3 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K
                (Theory2.trans K (Theory2.symm K Aₚ)
                  (Theory2.trans K leftComp A_q))
                (Theory2.whiskerLeft K σ cq)))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.whiskerLeft K σ leftRest)
                (Theory2.whiskerLeft K σ cq))) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
          (Theory3.transCongrLeft K h3Inner (Theory2.whiskerLeft K σ cq))
      have h4 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.whiskerLeft K σ leftRest)
                (Theory2.whiskerLeft K σ cq)))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq))) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
          (Theory3.symm K (Theory3.whiskerLeftTrans K σ leftRest cq))
      have h5 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq)))
            (Theory2.trans K
              (Theory2.whiskerLeft K σ (Theory2.symm K cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq))) :=
        Theory3.transCongrLeft K (Theory3.invWhiskerLeft K σ cp)
          (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq))
      have h6 :
          Theory3 K
            (Theory2.trans K
              (Theory2.whiskerLeft K σ (Theory2.symm K cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq)))
            (Theory2.whiskerLeft K σ
              (Theory2.trans K (Theory2.symm K cp)
                (Theory2.trans K leftRest cq))) :=
        Theory3.symm K
          (Theory3.whiskerLeftTrans K σ (Theory2.symm K cp)
            (Theory2.trans K leftRest cq))
      have h7 :
          Theory3 K
            (Theory2.whiskerLeft K σ
              (Theory2.trans K (Theory2.symm K cp)
                (Theory2.trans K leftRest cq)))
            (Theory2.whiskerLeft K σ
              (reductionSeq_whiskerLeft_in_Theory2 K rest η)) :=
        Theory3.whiskerLeftCongr K σ
          (reductionSeq_whiskerLeft_shell_to_struct_in_Theory3 K rest η)
      simpa [σ, ρ, cp, cq, Aₚ, A_q, leftRest, leftComp, reductionSeq_comp_in_Theory2,
        reductionSeq_in_Theory1, reductionSeq_whiskerLeft_in_Theory2] using
        Theory3.trans K h0
          (Theory3.trans K h1
            (Theory3.trans K h2
              (Theory3.trans K h3
                (Theory3.trans K h4 (Theory3.trans K h5 (Theory3.trans K h6 h7))))))
  | _, _, _, .stepInv s rest, p, q, η => by
      let σ := betaEtaStepInv_in_Theory1 K _ _ s
      let ρ := reductionSeq_in_Theory1 K rest
      let cp := reductionSeq_comp_in_Theory2 K rest p
      let cq := reductionSeq_comp_in_Theory2 K rest q
      let Aₚ := Theory2.associator K σ ρ (reductionSeq_in_Theory1 K p)
      let A_q := Theory2.associator K σ ρ (reductionSeq_in_Theory1 K q)
      let leftRest := Theory2.whiskerLeft K ρ η
      let leftComp := Theory2.whiskerLeft K (Theory1.comp K σ ρ) η
      have h0 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (reductionSeq_comp_in_Theory2 K (.stepInv s rest) p))
              (Theory2.trans K
                (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K (.stepInv s rest)) η)
                (reductionSeq_comp_in_Theory2 K (.stepInv s rest) q)))
            (Theory2.trans K
              (Theory2.trans K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
                (Theory2.symm K Aₚ))
              (Theory2.trans K leftComp
                (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))) := by
        exact Theory3.transCongrLeft K
          (by
            simpa [σ, ρ, cp, Aₚ, reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1]
              using Theory3.symmTrans K Aₚ (Theory2.whiskerLeft K σ cp))
          (Theory2.trans K leftComp
            (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))
      have h1 :
          Theory3 K
            (Theory2.trans K
              (Theory2.trans K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
                (Theory2.symm K Aₚ))
              (Theory2.trans K leftComp
                (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq))))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.symm K Aₚ)
                (Theory2.trans K leftComp
                  (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq))))) := by
        exact Theory3.transAssoc K
          (Theory2.symm K (Theory2.whiskerLeft K σ cp))
          (Theory2.symm K Aₚ)
          (Theory2.trans K leftComp
            (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))
      have h2Inner :
          Theory3 K
            (Theory2.trans K (Theory2.symm K Aₚ)
              (Theory2.trans K leftComp
                (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq))))
            (Theory2.trans K
              (Theory2.trans K (Theory2.symm K Aₚ)
                (Theory2.trans K leftComp A_q))
              (Theory2.whiskerLeft K σ cq)) := by
        exact Theory3.trans K
          (Theory3.transCongrRight K (Theory2.symm K Aₚ)
            (Theory3.symm K
              (Theory3.transAssoc K leftComp A_q
                (Theory2.whiskerLeft K σ cq))))
          (Theory3.symm K
            (Theory3.transAssoc K (Theory2.symm K Aₚ)
              (Theory2.trans K leftComp A_q)
              (Theory2.whiskerLeft K σ cq)))
      have h2 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.symm K Aₚ)
                (Theory2.trans K leftComp
                  (Theory2.trans K A_q (Theory2.whiskerLeft K σ cq)))))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K
                (Theory2.trans K (Theory2.symm K Aₚ)
                  (Theory2.trans K leftComp A_q))
                (Theory2.whiskerLeft K σ cq))) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.whiskerLeft K σ cp)) h2Inner
      have h3Inner :
          Theory3 K
            (Theory2.trans K (Theory2.symm K Aₚ)
              (Theory2.trans K leftComp A_q))
            (Theory2.whiskerLeft K σ leftRest) := by
        exact Theory3.whiskerLeftCompShell K σ ρ η
      have h3 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K
                (Theory2.trans K (Theory2.symm K Aₚ)
                  (Theory2.trans K leftComp A_q))
                (Theory2.whiskerLeft K σ cq)))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.whiskerLeft K σ leftRest)
                (Theory2.whiskerLeft K σ cq))) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
          (Theory3.transCongrLeft K h3Inner (Theory2.whiskerLeft K σ cq))
      have h4 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.trans K (Theory2.whiskerLeft K σ leftRest)
                (Theory2.whiskerLeft K σ cq)))
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq))) :=
        Theory3.transCongrRight K (Theory2.symm K (Theory2.whiskerLeft K σ cp))
          (Theory3.symm K (Theory3.whiskerLeftTrans K σ leftRest cq))
      have h5 :
          Theory3 K
            (Theory2.trans K
              (Theory2.symm K (Theory2.whiskerLeft K σ cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq)))
            (Theory2.trans K
              (Theory2.whiskerLeft K σ (Theory2.symm K cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq))) :=
        Theory3.transCongrLeft K (Theory3.invWhiskerLeft K σ cp)
          (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq))
      have h6 :
          Theory3 K
            (Theory2.trans K
              (Theory2.whiskerLeft K σ (Theory2.symm K cp))
              (Theory2.whiskerLeft K σ (Theory2.trans K leftRest cq)))
            (Theory2.whiskerLeft K σ
              (Theory2.trans K (Theory2.symm K cp)
                (Theory2.trans K leftRest cq))) :=
        Theory3.symm K
          (Theory3.whiskerLeftTrans K σ (Theory2.symm K cp)
            (Theory2.trans K leftRest cq))
      have h7 :
          Theory3 K
            (Theory2.whiskerLeft K σ
              (Theory2.trans K (Theory2.symm K cp)
                (Theory2.trans K leftRest cq)))
            (Theory2.whiskerLeft K σ
              (reductionSeq_whiskerLeft_in_Theory2 K rest η)) :=
        Theory3.whiskerLeftCongr K σ
          (reductionSeq_whiskerLeft_shell_to_struct_in_Theory3 K rest η)
      simpa [σ, ρ, cp, cq, Aₚ, A_q, leftRest, leftComp, reductionSeq_comp_in_Theory2,
        reductionSeq_in_Theory1, reductionSeq_whiskerLeft_in_Theory2] using
        Theory3.trans K h0
          (Theory3.trans K h1
            (Theory3.trans K h2
              (Theory3.trans K h3
                (Theory3.trans K h4 (Theory3.trans K h5 (Theory3.trans K h6 h7))))))

/-- Interpreting a syntactic left whisker agrees with the comparison shell built
from semantic left whiskering and the explicit-composition bridges. -/
noncomputable def homotopy2_whiskerLeft_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (homotopy2_in_Theory2 K (HigherTerms.whiskerLeft r α))
      (Theory2.trans K
        (Theory2.symm K (reductionSeq_comp_in_Theory2 K r p))
        (Theory2.trans K
          (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α))
          (reductionSeq_comp_in_Theory2 K r q))) :=
  Theory3.symm K (reductionSeq_whiskerLeft_shell_to_struct_in_Theory3 K r (homotopy2_in_Theory2 K α))

/-- Left whiskering commutes with symmetry for interpreted explicit 2-cells. -/
noncomputable def homotopy2_whiskerLeftSymm_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.symm K (homotopy2_in_Theory2 K α)))
      (Theory2.symm K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
          (homotopy2_in_Theory2 K α))) :=
  Theory3.whiskerLeftSymm K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)

/-- The inverse direction of left-whisker symmetry for interpreted explicit
2-cells. -/
noncomputable def homotopy2_invWhiskerLeft_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (Theory2.symm K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
          (homotopy2_in_Theory2 K α)))
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.symm K (homotopy2_in_Theory2 K α))) :=
  Theory3.invWhiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)

/-- Right whiskering commutes with vertical composition for interpreted explicit
2-cells. -/
noncomputable def homotopy2_whiskerRightTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q s : ReductionSeq L M} (α : Homotopy2 p q) (β : Homotopy2 q s)
    (r : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.trans K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β))
        (reductionSeq_in_Theory1 K r))
      (Theory2.trans K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α)
          (reductionSeq_in_Theory1 K r))
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K β)
          (reductionSeq_in_Theory1 K r))) :=
  Theory3.whiskerRightTrans K
    (homotopy2_in_Theory2 K α)
    (homotopy2_in_Theory2 K β)
    (reductionSeq_in_Theory1 K r)

/-- Right whiskering commutes with symmetry for interpreted explicit 2-cells. -/
noncomputable def homotopy2_whiskerRightSymm_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.symm K (homotopy2_in_Theory2 K α))
        (reductionSeq_in_Theory1 K s))
      (Theory2.symm K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α)
          (reductionSeq_in_Theory1 K s))) :=
  Theory3.whiskerRightSymm K (homotopy2_in_Theory2 K α)
    (reductionSeq_in_Theory1 K s)

/-- The inverse direction of right-whisker symmetry for interpreted explicit
2-cells. -/
noncomputable def homotopy2_invWhiskerRight_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.symm K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α)
          (reductionSeq_in_Theory1 K s)))
       (Theory2.whiskerRight K
         (Theory2.symm K (homotopy2_in_Theory2 K α))
         (reductionSeq_in_Theory1 K s)) :=
  Theory3.invWhiskerRight K (homotopy2_in_Theory2 K α)
    (reductionSeq_in_Theory1 K s)

/-- Right composition with an interpreted explicit 2-cell followed by its inverse
normalizes to the reflexive source 2-cell. -/
noncomputable def homotopy2_transRightCancel_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (Theory2.trans K
        (homotopy2_in_Theory2 K α)
        (Theory2.symm K (homotopy2_in_Theory2 K α)))
      (Theory2.refl K (reductionSeq_in_Theory1 K p)) :=
  Theory3.transRightCancel K (homotopy2_in_Theory2 K α)

/-- Left composition with the inverse of an interpreted explicit 2-cell
normalizes to the reflexive target 2-cell. -/
noncomputable def homotopy2_transLeftCancel_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.symm K (homotopy2_in_Theory2 K α))
        (homotopy2_in_Theory2 K α))
      (Theory2.refl K (reductionSeq_in_Theory1 K q)) :=
  Theory3.transLeftCancel K (homotopy2_in_Theory2 K α)

/-- Triangle coherence for interpreted explicit paths. -/
noncomputable def reductionSeq_triangle_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_associator_in_Theory2 K p (ReductionSeq.refl M) q)
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p)
          (reductionSeq_leftUnitor_in_Theory2 K q)))
      (Theory2.whiskerRight K
        (reductionSeq_rightUnitor_in_Theory2 K p)
        (reductionSeq_in_Theory1 K q)) :=
  Theory3.triangle K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)

/-- Right whiskering of an interpreted explicit 2-cell carries an explicit
semantic tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerRight_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K s)))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K s)))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K s))
      (Theory1.whiskerRightTriangle K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K s)) :=
  Theory3.whiskerRightTetrahedron K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K s)

/-- Left whiskering preserves reflexive interpreted 2-cells up to a semantic
3-cell, obtained by comparing the two boundary-aware tetrahedra with matching
outer boundary. -/
noncomputable def homotopy2_whiskerLeftRefl_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) (p : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.refl K (reductionSeq_in_Theory1 K p)))
      (Theory2.refl K
        (Theory1.comp K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K p))) :=
  TheoryTetrahedron.path3 K
    (homotopy2_whiskerLeft_in_TheoryTetrahedron K r (Homotopy2.refl p))
    (reductionSeq_comp_refl_in_TheoryTetrahedron K r p)

/-- Structural left whiskering of a reflexive interpreted 2-cell along an
explicit βη path normalizes directly to the reflexive interpreted composite
path. The recursive structural whisker appears as the front face of the
single-step whiskering tetrahedron, while the target tetrahedron has the
reflexive front face coming from the recursive normalization. -/
noncomputable def reductionSeq_whiskerLeftRefl_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → (p : ReductionSeq M N) →
      Theory3 K
        (reductionSeq_whiskerLeft_in_Theory2 K r
          (Theory2.refl K (reductionSeq_in_Theory1 K p)))
        (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat r p)))
  | _, _, _, .refl _, p =>
      Theory3.refl K (Theory2.refl K (reductionSeq_in_Theory1 K p))
  | _, _, _, .step s rest, p =>
      TheoryTetrahedron.frontPath3 K
        (reductionSeq_whiskerLeftRefl_in_Theory3 K rest p)
        (Theory3.whiskerLeftTetrahedron K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest
            (Theory2.refl K (reductionSeq_in_Theory1 K p))))
        (TheoryTriangle.reflTetrahedron K
          (Theory1.compTriangle K (betaEtaStep_in_Theory1 K _ _ s)
            (reductionSeq_in_Theory1 K (ReductionSeq.concat rest p))))
  | _, _, _, .stepInv s rest, p =>
      TheoryTetrahedron.frontPath3 K
        (reductionSeq_whiskerLeftRefl_in_Theory3 K rest p)
        (Theory3.whiskerLeftTetrahedron K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest
            (Theory2.refl K (reductionSeq_in_Theory1 K p))))
        (TheoryTriangle.reflTetrahedron K
          (Theory1.compTriangle K (betaEtaStepInv_in_Theory1 K _ _ s)
            (reductionSeq_in_Theory1 K (ReductionSeq.concat rest p))))

/-- A first boundary-aware 4-simplex comparison for right whiskering of a
reflexive interpreted 2-cell. This absorbs the mismatch between the source and
target tetrahedra into an explicit extra boundary face, but does not yet
normalize all the way into `Theory3`. -/
noncomputable def homotopy2_whiskerRightRefl_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s)))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s))) :=
  TheoryTetrahedron.comparison K
    (homotopy2_whiskerRight_in_TheoryTetrahedron K (Homotopy2.refl p) s)
    (reductionSeq_comp_refl_in_TheoryTetrahedron K p s)
    (homotopy2_whiskerRight_in_TheoryTetrahedron K (Homotopy2.refl p) s)

/-- The normalized bridge tetrahedron for `whiskerRightRefl`, obtained by
reading the explicit simplicial bridge `K.whiskerRightReflPath3` back as a
boundary-aware semantic tetrahedron. Unlike the first comparison above, its
fourth face is already the reflexive 2-cell on the composite. -/
noncomputable def homotopy2_whiskerRightRefl_bridge_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s)))) :=
  fun ρ =>
    (K.whiskerRightReflPath3 (reductionSeq_in_Theory1 K p ρ)
      (reductionSeq_in_Theory1 K s ρ)).toTetrahedron

/-- Right whiskering preserves reflexive interpreted 2-cells up to a semantic
3-cell. This is the final normalized witness extracted from the bridge
tetrahedron above. -/
noncomputable def homotopy2_whiskerRightRefl_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.refl K (reductionSeq_in_Theory1 K p))
        (reductionSeq_in_Theory1 K s))
      (Theory2.refl K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))) :=
  fun ρ =>
    K.whiskerRightReflPath3 (reductionSeq_in_Theory1 K p ρ)
      (reductionSeq_in_Theory1 K s ρ)

/-- Naming wrapper for the normalized `whiskerRightRefl` simplification step,
for the standalone semantic right-whisker normalization witness. -/
noncomputable def reductionSeq_whiskerRight_refl_simplify_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.refl K (reductionSeq_in_Theory1 K p))
        (reductionSeq_in_Theory1 K s))
      (Theory2.refl K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))) :=
  homotopy2_whiskerRightRefl_in_Theory3 K p s

/-- The inner composite in the legacy structural right-whisker reflexivity
shell normalizes to the comparison 2-cell `c`. This isolates the final
cancellation step for the unnormalized structural shell. -/
noncomputable def reductionSeq_whiskerRight_refl_inner_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s))
        (reductionSeq_comp_in_Theory2 K p s))
      (reductionSeq_comp_in_Theory2 K p s) :=
  Theory3.trans K
    (Theory3.transCongrLeft K
      (reductionSeq_whiskerRight_refl_simplify_in_Theory3 K p s)
      (reductionSeq_comp_in_Theory2 K p s))
    (Theory3.transReflLeft K (reductionSeq_comp_in_Theory2 K p s))

/-- The full legacy structural right-whisker reflexivity shell contracts to the
reflexive semantic 2-cell on the interpreted concatenation. -/
noncomputable def reductionSeq_whiskerRight_refl_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K
        (Theory2.refl K (reductionSeq_in_Theory1 K p)) s)
      (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))) := by
  let c := reductionSeq_comp_in_Theory2 K p s
  exact Theory3.trans K
    (Theory3.transCongrRight K (Theory2.symm K c)
      (reductionSeq_whiskerRight_refl_inner_in_Theory3 K p s))
    (Theory3.transLeftCancel K c)

/-- Interpreting a syntactic right whisker agrees with the legacy structural
right-whisker semantic shell, up to a semantic 3-cell. The only nontrivial
case is the reflexive input, where the direct interpreter normalizes eagerly. -/
noncomputable def homotopy2Deriv_whiskerRight_bridge_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → {p q : ReductionSeq L M} →
      (α : Homotopy2Deriv p q) → (s : ReductionSeq M N) →
        Theory3 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerRight α s))
          (reductionSeq_whiskerRight_in_Theory2 K (homotopy2Deriv_in_Theory2 K α) s)
  | _, _, _, _, _, .refl p, s =>
      Theory3.trans K
        (homotopy2_whiskerRight_refl_source_bridge_in_Theory3 K p s)
        (Theory3.symm K (reductionSeq_whiskerRight_refl_bridge_in_Theory3 K p s))
  | _, _, _, _, _, .ofEq h, s => by
      change Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.ofEq h)) s)
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.ofEq h)) s)
      exact Theory3.refl K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.ofEq h)) s)
  | _, _, _, _, _, .symm α, s => by
      change Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.symm α)) s)
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.symm α)) s)
      exact Theory3.refl K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.symm α)) s)
  | _, _, _, _, _, .trans α β, s => by
      change Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.trans α β)) s)
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.trans α β)) s)
      exact Theory3.refl K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.trans α β)) s)
  | _, _, _, _, _, .diamond p₁ p₂ q₁ q₂, s => by
      change Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.diamond p₁ p₂ q₁ q₂)) s)
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.diamond p₁ p₂ q₁ q₂)) s)
      exact Theory3.refl K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.diamond p₁ p₂ q₁ q₂)) s)
  | _, _, _, _, _, .whiskerLeft r α, s => by
      change Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerLeft r α)) s)
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerLeft r α)) s)
      exact Theory3.refl K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerLeft r α)) s)
  | _, _, _, _, _, .whiskerRight α r, s => by
      change Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerRight α r)) s)
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerRight α r)) s)
      exact Theory3.refl K
        (reductionSeq_whiskerRight_in_Theory2 K
          (homotopy2Deriv_in_Theory2 K (Homotopy2Deriv.whiskerRight α r)) s)

/-- Interpreting a syntactic right whisker agrees with the legacy structural
right-whisker semantic shell, up to a semantic 3-cell. -/
noncomputable def homotopy2_whiskerRight_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (whiskerRight α s))
      (reductionSeq_whiskerRight_in_Theory2 K (homotopy2_in_Theory2 K α) s) :=
  homotopy2Deriv_whiskerRight_bridge_in_Theory3 K α.deriv s

/-- Interpreting the primitive syntactic `interchange'` 3-cell amounts to
conjugating the normalized semantic `interchange'` witness by the structural
comparison shells for left and right whiskering. -/
noncomputable def homotopy2_interchange'_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Theory3 K
      (homotopy2_in_Theory2 K (HigherTerms.hcomp α β))
      (homotopy2_in_Theory2 K
        (Homotopy2.trans (HigherTerms.whiskerLeft p β)
          (HigherTerms.whiskerRight α q'))) := by
  let η := homotopy2_in_Theory2 K α
  let θ := homotopy2_in_Theory2 K β
  let cₛ := reductionSeq_comp_in_Theory2 K p q
  let cₘ := reductionSeq_comp_in_Theory2 K p' q
  let cₘ' := reductionSeq_comp_in_Theory2 K p q'
  let cₜ := reductionSeq_comp_in_Theory2 K p' q'
  let leftSource := reductionSeq_whiskerLeft_shell_in_Theory2 K p' θ
  let leftTarget := reductionSeq_whiskerLeft_shell_in_Theory2 K p θ
  have hSourceShell :
      Theory3 K
        (homotopy2_in_Theory2 K (HigherTerms.hcomp α β))
        (Theory2.trans K (Theory2.symm K cₛ)
          (Theory2.trans K (Theory2.hcomp K η θ) cₜ)) := by
    change Theory3 K
      (Theory2.trans K
        (homotopy2_in_Theory2 K (HigherTerms.whiskerRight α q))
        (reductionSeq_whiskerLeft_in_Theory2 K p' θ))
      (Theory2.trans K (Theory2.symm K cₛ)
        (Theory2.trans K (Theory2.hcomp K η θ) cₜ))
    have hPieces :
        Theory3 K
          (Theory2.trans K
            (homotopy2_in_Theory2 K (HigherTerms.whiskerRight α q))
            (reductionSeq_whiskerLeft_in_Theory2 K p' θ))
          (Theory2.trans K
            (reductionSeq_whiskerRight_in_Theory2 K η q)
            leftSource) := by
      exact Theory3.trans K
        (Theory3.transCongrLeft K
          (homotopy2_whiskerRight_bridge_in_Theory3 K α q)
          (reductionSeq_whiskerLeft_in_Theory2 K p' θ))
        (Theory3.transCongrRight K
          (reductionSeq_whiskerRight_in_Theory2 K η q)
          (by
            simpa [leftSource, reductionSeq_whiskerLeft_shell_in_Theory2] using
              homotopy2_whiskerLeft_bridge_in_Theory3 K p' β))
    have hCompose :
        Theory3 K
          (Theory2.trans K
            (reductionSeq_whiskerRight_in_Theory2 K η q)
            leftSource)
          (Theory2.trans K (Theory2.symm K cₛ)
            (Theory2.trans K (Theory2.hcomp K η θ) cₜ)) := by
      simpa [cₛ, cₘ, cₜ, leftSource, reductionSeq_whiskerLeft_shell_in_Theory2,
        reductionSeq_whiskerRight_in_Theory2, Theory2.hcomp] using
        comparisonShellCompose_in_Theory3 K cₛ
          (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K q))
          cₘ
          (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p') θ)
          cₜ
    exact Theory3.trans K hPieces hCompose
  have hInterchange :
      Theory3 K
        (Theory2.trans K (Theory2.symm K cₛ)
          (Theory2.trans K (Theory2.hcomp K η θ) cₜ))
        (Theory2.trans K (Theory2.symm K cₛ)
          (Theory2.trans K
            (Theory2.trans K
              (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) θ)
              (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K q')))
            cₜ)) := by
    exact Theory3.transCongrRight K (Theory2.symm K cₛ)
      (Theory3.transCongrLeft K (homotopy2_interchange'_in_Theory3 K α β) cₜ)
  have hTargetShell :
      Theory3 K
        (homotopy2_in_Theory2 K
          (Homotopy2.trans (HigherTerms.whiskerLeft p β)
            (HigherTerms.whiskerRight α q')))
        (Theory2.trans K (Theory2.symm K cₛ)
          (Theory2.trans K
            (Theory2.trans K
              (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) θ)
              (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K q')))
            cₜ)) := by
    change Theory3 K
      (Theory2.trans K
        (reductionSeq_whiskerLeft_in_Theory2 K p θ)
        (homotopy2_in_Theory2 K (HigherTerms.whiskerRight α q')))
      (Theory2.trans K (Theory2.symm K cₛ)
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) θ)
            (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K q')))
          cₜ))
    have hPieces :
        Theory3 K
          (Theory2.trans K
            (reductionSeq_whiskerLeft_in_Theory2 K p θ)
            (homotopy2_in_Theory2 K (HigherTerms.whiskerRight α q')))
          (Theory2.trans K
            leftTarget
            (reductionSeq_whiskerRight_in_Theory2 K η q')) := by
      exact Theory3.trans K
        (Theory3.transCongrLeft K
          (by
            simpa [leftTarget, reductionSeq_whiskerLeft_shell_in_Theory2] using
              homotopy2_whiskerLeft_bridge_in_Theory3 K p β)
          (homotopy2_in_Theory2 K (HigherTerms.whiskerRight α q')))
        (Theory3.transCongrRight K leftTarget
          (homotopy2_whiskerRight_bridge_in_Theory3 K α q'))
    have hCompose :
        Theory3 K
          (Theory2.trans K
            leftTarget
            (reductionSeq_whiskerRight_in_Theory2 K η q'))
          (Theory2.trans K (Theory2.symm K cₛ)
            (Theory2.trans K
              (Theory2.trans K
                (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) θ)
                (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K q')))
              cₜ)) := by
      simpa [cₛ, cₘ', cₜ, leftTarget, reductionSeq_whiskerLeft_shell_in_Theory2,
        reductionSeq_whiskerRight_in_Theory2] using
        comparisonShellCompose_in_Theory3 K cₛ
          (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) θ)
          cₘ'
          (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K q'))
          cₜ
    exact Theory3.trans K hPieces hCompose
  exact Theory3.trans K hSourceShell
    (Theory3.trans K hInterchange (Theory3.symm K hTargetShell))

/-- When the right-whiskered 2-cell is equality-generated, the structural
right-whisker shell contracts to the corresponding equality-generated 2-cell on
the concatenated explicit paths. This isolates the target-side endpoint bridge
needed for primitive triangle- and pentagon-style coherence cells whose
right-whiskered factor is an `ofEq` witness. -/
noncomputable def reductionSeq_whiskerRightOfEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term} {p q : ReductionSeq L M}
    (h : p = q) (s : ReductionSeq M N) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K
        (Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h)) s)
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (congrArg (fun r => ReductionSeq.concat r s) h))) := by
  cases h
  simpa using reductionSeq_whiskerRight_refl_bridge_in_Theory3 K p s

/-- Specialized endpoint bridge for right whiskering an equality-generated
syntactic 2-cell: the interpreted structural shell contracts to the
equality-generated 2-cell on the concatenated explicit paths. -/
noncomputable def homotopy2_whiskerRightOfEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term} {p q : ReductionSeq L M}
    (h : p = q) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerRight (HigherTerms.Homotopy2.ofEq h) s))
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (congrArg (fun r => ReductionSeq.concat r s) h))) := by
  exact Theory3.trans K
    (Theory3.ofEq K (homotopy2_in_Theory2_whiskerRight_ofEq K h s))
    (reductionSeq_whiskerRightOfEq_toOfEq_in_Theory3 K h s)

/-- When the left-whiskered 2-cell is equality-generated, the structural
left-whisker shell contracts to the corresponding equality-generated 2-cell on
the concatenated explicit paths. -/
noncomputable def reductionSeq_whiskerLeftOfEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N}
    (h : p = q) :
    Theory3 K
      (reductionSeq_whiskerLeft_in_Theory2 K r
        (Theory2.ofEq K (congrArg (fun t => reductionSeq_in_Theory1 K t) h)))
      (Theory2.ofEq K
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (congrArg (fun t => ReductionSeq.concat r t) h))) := by
  cases h
  simpa using reductionSeq_whiskerLeftRefl_in_Theory3 K r p

/-- Specialized endpoint bridge for left whiskering an equality-generated
syntactic 2-cell: the interpreted structural shell contracts to the
equality-generated 2-cell on the concatenated explicit paths. -/
noncomputable def homotopy2_whiskerLeftOfEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N}
    (h : p = q) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerLeft r (HigherTerms.Homotopy2.ofEq h)))
      (Theory2.ofEq K
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (congrArg (fun t => ReductionSeq.concat r t) h))) := by
  exact Theory3.trans K
    (Theory3.ofEq K (homotopy2_in_Theory2_whiskerLeft_ofEq K r h))
    (reductionSeq_whiskerLeftOfEq_toOfEq_in_Theory3 K r h)

/-- Pure semantic left whiskering preserves the reflexive associator comparison.

Unlike `reductionSeq_comp_associator_refl_whiskerLeft_toOfEq_in_Theory3`, this
does not insert the explicit-composition comparison cells coming from
`reductionSeq_whiskerLeft_in_Theory2`; it is just the direct
`Theory2.whiskerLeft` image of the base reflexive associator shell. -/
noncomputable def reductionSeq_comp_associator_refl_theoryWhiskerLeft_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (Theory2.whiskerLeft K α
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.ofEq K
        (congrArg (fun δ => Theory1.comp K α δ)
          (congrArg (fun t => reductionSeq_in_Theory1 K t)
            (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)))) := by
  exact Theory3.whiskerLeftCongrOfEq K α
    (congrArg (fun t => reductionSeq_in_Theory1 K t)
      (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r))
    (reductionSeq_comp_associator_refl_in_Theory3 K q r)

/-- The pure semantic left whisker of the reflexive associator shell is already
a contractible loop at the right-associated composite. This packages the
`Theory3.whiskerLeftCongr` probe result at theorem level, separated from the
explicit-path whisker shell theorems below. -/
noncomputable def reductionSeq_comp_associator_refl_theoryWhiskerLeft_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (Theory2.whiskerLeft K α
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.refl K
        (Theory1.comp K α
          (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))) := by
  let hEq :
      congrArg (fun δ => Theory1.comp K α δ)
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)) = rfl := by
    exact Subsingleton.elim _ _
  exact Theory3.trans K
    (reductionSeq_comp_associator_refl_theoryWhiskerLeft_toOfEq_in_Theory3 K α q r)
    (Theory3.ofEq K (by
      cases hEq
      rfl))

/-- Right whiskering preserves the contraction of the pure semantic left whisker
of the reflexive associator shell. With `Theory3.whiskerRightCongr` available,
no auxiliary triangle-comparison hypothesis is needed anymore. -/
noncomputable def reductionSeq_comp_associator_refl_theoryWhiskerLeft_rightWhisker_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (α : Theory1 K L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.whiskerLeft K α
          (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
        (reductionSeq_in_Theory1 K s))
      (Theory2.refl K
        (Theory1.comp K
          (Theory1.comp K α
            (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))
          (reductionSeq_in_Theory1 K s))) := by
  let η :=
    Theory2.whiskerLeft K α
      (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r)
  let θ :=
    Theory2.refl K
      (Theory1.comp K α
        (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))
  let δ := reductionSeq_in_Theory1 K s
  exact Theory3.trans K
    (Theory3.whiskerRightCongr K
      (reductionSeq_comp_associator_refl_theoryWhiskerLeft_in_Theory3 K α q r)
      δ)
    (Theory3.whiskerRightRefl K
      (Theory1.comp K α
        (reductionSeq_in_Theory1 K (ReductionSeq.concat q r)))
      δ)

/-- Left whiskering the reflexive associator shell already contracts to the
equality-generated whiskered associator on the concatenated explicit paths. -/
noncomputable def reductionSeq_comp_associator_refl_whiskerLeft_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_whiskerLeft_shell_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.ofEq K
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (congrArg (fun t => ReductionSeq.concat p t)
            (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)))) := by
  exact Theory3.trans K
    (reductionSeq_whiskerLeft_shell_to_struct_in_Theory3 K p
      (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
    (Theory3.trans K
      (reductionSeq_whiskerLeftCongr_in_Theory3 K p
        (reductionSeq_comp_associator_refl_in_Theory3 K q r))
      (reductionSeq_whiskerLeftOfEq_toOfEq_in_Theory3 K p
        (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)))

/-- The left-whiskered reflexive associator shell is in fact a contractible loop
at the right-associated whiskered path. This is the normalized close variant of
the tempting but ill-typed comparison with `reductionSeq_associator_shell_in_Theory2`:
after left whiskering, the reflexive associator shell has identical source and
target endpoints, so the right statement is that it collapses to reflexivity. -/
noncomputable def reductionSeq_comp_associator_refl_whiskerLeft_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_whiskerLeft_shell_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.refl K
        (reductionSeq_in_Theory1 K (ReductionSeq.concat p (ReductionSeq.concat q r)))) := by
  let hEq :
      congrArg (fun t => reductionSeq_in_Theory1 K t)
        (congrArg (fun t => ReductionSeq.concat p t)
          (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)) = rfl := by
    exact Subsingleton.elim _ _
  exact Theory3.trans K
    (reductionSeq_comp_associator_refl_whiskerLeft_toOfEq_in_Theory3 K p q r)
    (Theory3.ofEq K (by
      cases hEq
      rfl))

/-- The semantic explicit left whisker of the reflexive associator shell is also
a comparison to the equality-generated whiskered associator on the concatenated
explicit paths. This is the semantic-interface counterpart of
`reductionSeq_comp_associator_refl_whiskerLeft_toOfEq_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_refl_semanticWhiskerLeft_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.ofEq K
        (congrArg (fun t => reductionSeq_in_Theory1 K t)
          (congrArg (fun t => ReductionSeq.concat p t)
            (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)))) := by
  exact Theory3.trans K
    (Theory3.symm K
      (reductionSeq_whiskerLeft_shell_to_struct_in_Theory3 K p
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r)))
    (reductionSeq_comp_associator_refl_whiskerLeft_toOfEq_in_Theory3 K p q r)

/-- The semantic explicit left whisker of the reflexive associator shell is also
a contractible loop at the right-associated whiskered path. This packages the
new structural whiskered-refl contraction behind the standard
`reductionSeq_whiskerLeft_in_Theory2` interface. -/
noncomputable def reductionSeq_comp_associator_refl_semanticWhiskerLeft_in_Theory3
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K (ReductionSeq.refl M) q r))
      (Theory2.refl K
        (reductionSeq_in_Theory1 K (ReductionSeq.concat p (ReductionSeq.concat q r)))) := by
  let hEq :
      congrArg (fun t => reductionSeq_in_Theory1 K t)
        (congrArg (fun t => ReductionSeq.concat p t)
          (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)) = rfl := by
    exact Subsingleton.elim _ _
  exact Theory3.trans K
    (reductionSeq_comp_associator_refl_semanticWhiskerLeft_toOfEq_in_Theory3 K p q r)
    (Theory3.ofEq K (by
      cases hEq
      rfl))

/-- The target side of the primitive triangle 3-cell already bridges from the
interpreted structural right-whisker shell to the equality-generated 2-cell on
the concatenated explicit paths. -/
noncomputable def homotopy2_triangle_target_ofEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerRight (HigherTerms.rightUnitor p) q))
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (congrArg (fun r => ReductionSeq.concat r q)
            (ReductionSeq.concat_refl_right p)))) := by
  simpa [HigherTerms.rightUnitor] using
    (homotopy2_whiskerRightOfEq_toOfEq_in_Theory3 K
      (ReductionSeq.concat_refl_right p) q)

/-- The source side of the primitive triangle 3-cell already agrees with the
structural shell built from the explicit associator equality and the structural
left-unitor shell. This keeps the left-unitor comparison explicit instead of
collapsing it immediately to reflexivity. -/
noncomputable def homotopy2_triangle_source_shell_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (Homotopy2.trans (HigherTerms.associator p (ReductionSeq.refl M) q)
          (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q))))
      (Theory2.trans K
        (Theory2.ofEq K
          (congrArg (fun r => reductionSeq_in_Theory1 K r)
            (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_leftUnitor_shell_in_Theory2 K q))) := by
  change Theory3 K
    (Theory2.trans K
      (homotopy2_in_Theory2 K
        (HigherTerms.associator p (ReductionSeq.refl M) q))
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (homotopy2_in_Theory2 K (HigherTerms.leftUnitor q))))
    (Theory2.trans K
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (reductionSeq_leftUnitor_shell_in_Theory2 K q)))
  have hAssoc :
      Theory3 K
        (homotopy2_in_Theory2 K
          (HigherTerms.associator p (ReductionSeq.refl M) q))
        (Theory2.ofEq K
          (congrArg (fun r => reductionSeq_in_Theory1 K r)
            (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q))) := by
    simpa [HigherTerms.associator] using
      (Theory3.ofEq K
        (homotopy2_in_Theory2_ofEq K
          (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
  exact Theory3.trans K
    (Theory3.transCongrLeft K hAssoc
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (homotopy2_in_Theory2 K (HigherTerms.leftUnitor q))))
    (Theory3.transCongrRight K
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
      (homotopy2_whiskerLeft_leftUnitor_bridge_in_Theory3 K p q))

/-- The right-whiskered associator factor on the target side of the primitive
pentagon 3-cell already bridges from the interpreted structural right-whisker
shell to the equality-generated 2-cell on the concatenated explicit paths. -/
noncomputable def homotopy2_pentagon_rightWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (congrArg (fun u => ReductionSeq.concat u s)
            (ReductionSeq.concat_assoc p q r)))) := by
  simpa [HigherTerms.associator] using
    (homotopy2_whiskerRightOfEq_toOfEq_in_Theory3 K
      (ReductionSeq.concat_assoc p q r) s)

/-- The left-whiskered associator factor on the target side of the primitive
pentagon 3-cell already bridges from the interpreted structural left-whisker
shell to the equality-generated 2-cell on the concatenated explicit paths. -/
noncomputable def homotopy2_pentagon_leftWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerLeft p (HigherTerms.associator q r s)))
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (congrArg (fun u => ReductionSeq.concat p u)
            (ReductionSeq.concat_assoc q r s)))) := by
  simpa [HigherTerms.associator] using
    (homotopy2_whiskerLeftOfEq_toOfEq_in_Theory3 K p
      (ReductionSeq.concat_assoc q r s))

/-- The first normalization step for the structural right-whisker transitivity
shell replaces the inner whisker of a semantic composite by the composite of
the normalized whiskers, leaving only the remaining rebracketing and
comparison-shell insertion problem. -/
noncomputable def reductionSeq_whiskerRightTrans_head_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q r : ReductionSeq L M}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (θ : Theory2 K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
    (s : ReductionSeq M N) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K (Theory2.trans K η θ) s)
      (Theory2.trans K
        (Theory2.symm K (reductionSeq_comp_in_Theory2 K p s))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K s))
            (Theory2.whiskerRight K θ (reductionSeq_in_Theory1 K s)))
          (reductionSeq_comp_in_Theory2 K r s))) :=
  Theory3.transCongrRight K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K p s))
    (Theory3.transCongrLeft K
      (Theory3.whiskerRightTrans K η θ (reductionSeq_in_Theory1 K s))
      (reductionSeq_comp_in_Theory2 K r s))

/-- The full structural right-whisker transitivity shell contracts to the
composite of the structural right-whisker shells of the two factors. -/
noncomputable def reductionSeq_whiskerRightTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q r : ReductionSeq L M}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (θ : Theory2 K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
    (s : ReductionSeq M N) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K (Theory2.trans K η θ) s)
      (Theory2.trans K
        (reductionSeq_whiskerRight_in_Theory2 K η s)
        (reductionSeq_whiskerRight_in_Theory2 K θ s)) := by
  let c_p := reductionSeq_comp_in_Theory2 K p s
  let c_q := reductionSeq_comp_in_Theory2 K q s
  let c_r := reductionSeq_comp_in_Theory2 K r s
  let etaWhisk := Theory2.whiskerRight K η (reductionSeq_in_Theory1 K s)
  let thetaWhisk := Theory2.whiskerRight K θ (reductionSeq_in_Theory1 K s)
  have h_inner :
      Theory3 K
        (Theory2.trans K (Theory2.symm K c_p)
          (Theory2.trans K (Theory2.trans K etaWhisk thetaWhisk) c_r))
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_p) etaWhisk)
          (Theory2.trans K thetaWhisk c_r)) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K (Theory2.symm K c_p)
        (Theory3.transAssoc K etaWhisk thetaWhisk c_r))
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K c_p) etaWhisk
          (Theory2.trans K thetaWhisk c_r)))
  have h_insert_η :
      Theory3 K
        etaWhisk
        (Theory2.trans K
          (Theory2.trans K etaWhisk c_q)
          (Theory2.symm K c_q)) := by
    exact Theory3.trans K
      (Theory3.symm K (Theory3.transReflRight K etaWhisk))
      (Theory3.trans K
        (Theory3.transCongrRight K etaWhisk
          (Theory3.symm K (Theory3.transRightCancel K c_q)))
        (Theory3.symm K
          (Theory3.transAssoc K etaWhisk c_q (Theory2.symm K c_q))))
  have h_left_insert :
      Theory3 K
        (Theory2.trans K (Theory2.symm K c_p) etaWhisk)
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_p)
            (Theory2.trans K etaWhisk c_q))
          (Theory2.symm K c_q)) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K (Theory2.symm K c_p) h_insert_η)
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K c_p)
          (Theory2.trans K etaWhisk c_q)
          (Theory2.symm K c_q)))
  have h_finish :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_p) etaWhisk)
          (Theory2.trans K thetaWhisk c_r))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K c_p)
              (Theory2.trans K etaWhisk c_q))
            (Theory2.symm K c_q))
          (Theory2.trans K thetaWhisk c_r)) := by
    exact Theory3.transCongrLeft K h_left_insert
      (Theory2.trans K thetaWhisk c_r)
  have h_assoc_out :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.trans K (Theory2.symm K c_p)
              (Theory2.trans K etaWhisk c_q))
            (Theory2.symm K c_q))
          (Theory2.trans K thetaWhisk c_r))
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_p)
            (Theory2.trans K etaWhisk c_q))
          (Theory2.trans K (Theory2.symm K c_q)
            (Theory2.trans K thetaWhisk c_r))) := by
    exact Theory3.transAssoc K
      (Theory2.trans K (Theory2.symm K c_p)
        (Theory2.trans K etaWhisk c_q))
      (Theory2.symm K c_q)
      (Theory2.trans K thetaWhisk c_r)
  simpa [reductionSeq_whiskerRight_in_Theory2, c_p, c_q, c_r, etaWhisk, thetaWhisk] using
    Theory3.trans K
      (reductionSeq_whiskerRightTrans_head_in_Theory3 K η θ s)
      (Theory3.trans K
        h_inner
        (Theory3.trans K h_finish h_assoc_out))

/-- The full structural right-whisker symmetry shell contracts to the symmetry
of the original structural right-whisker shell. -/
noncomputable def reductionSeq_whiskerRightSymm_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (s : ReductionSeq M N) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K (Theory2.symm K η) s)
      (Theory2.symm K (reductionSeq_whiskerRight_in_Theory2 K η s)) := by
  let c_p := reductionSeq_comp_in_Theory2 K p s
  let c_q := reductionSeq_comp_in_Theory2 K q s
  let etaWhisk := Theory2.whiskerRight K η (reductionSeq_in_Theory1 K s)
  let etaWhiskSymm :=
    Theory2.whiskerRight K (Theory2.symm K η) (reductionSeq_in_Theory1 K s)
  let ss_cp := Theory2.symm K (Theory2.symm K c_p)
  have h_source_assoc :
      Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K (Theory2.symm K η) s)
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_q) etaWhiskSymm)
          c_p) := by
    simpa [reductionSeq_whiskerRight_in_Theory2, c_q, etaWhiskSymm] using
      (Theory3.symm K
        (Theory3.transAssoc K (Theory2.symm K c_q) etaWhiskSymm c_p))
  have h_source_ss :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_q) etaWhiskSymm)
          c_p)
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_q) etaWhiskSymm)
          ss_cp) := by
    exact Theory3.transCongrRight K
      (Theory2.trans K (Theory2.symm K c_q) etaWhiskSymm)
      (Theory3.symm K (Theory3.symmSymm K c_p))
  have h_target_outer :
      Theory3 K
        (Theory2.symm K (reductionSeq_whiskerRight_in_Theory2 K η s))
        (Theory2.trans K
          (Theory2.symm K (Theory2.trans K etaWhisk c_q))
          ss_cp) := by
    simpa [reductionSeq_whiskerRight_in_Theory2, c_p, etaWhisk, ss_cp] using
      (Theory3.symmTrans K (Theory2.symm K c_p)
        (Theory2.trans K etaWhisk c_q))
  have h_target_inner :
      Theory3 K
        (Theory2.trans K
          (Theory2.symm K (Theory2.trans K etaWhisk c_q))
          ss_cp)
        (Theory2.trans K
          (Theory2.trans K (Theory2.symm K c_q) etaWhiskSymm)
          ss_cp) := by
    let inner :=
      Theory3.transCongrLeft K
        (Theory3.symmTrans K etaWhisk c_q) ss_cp
    let whisk :=
      Theory3.transCongrLeft K
        (Theory3.transCongrRight K (Theory2.symm K c_q)
          (by
            simpa [etaWhisk, etaWhiskSymm] using
              (Theory3.invWhiskerRight K η (reductionSeq_in_Theory1 K s))))
        ss_cp
    exact Theory3.trans K inner whisk
  exact Theory3.trans K h_source_assoc
    (Theory3.trans K h_source_ss
      (Theory3.symm K (Theory3.trans K h_target_outer h_target_inner)))

/-- Any semantic comparison between pure right whiskers upgrades to the
corresponding comparison between the normalized explicit right-whisker shells. -/
noncomputable def reductionSeq_whiskerRightCongr_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M}
    {η θ : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)}
    (s : ReductionSeq M N)
    (hWhisk :
      Theory3 K
        (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K s))
        (Theory2.whiskerRight K θ (reductionSeq_in_Theory1 K s))) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K η s)
      (reductionSeq_whiskerRight_in_Theory2 K θ s) := by
  let c_p := reductionSeq_comp_in_Theory2 K p s
  let c_q := reductionSeq_comp_in_Theory2 K q s
  simpa [reductionSeq_whiskerRight_in_Theory2, c_p, c_q] using
    (Theory3.transCongrRight K
      (Theory2.symm K c_p)
      (Theory3.transCongrLeft K hWhisk c_q))

/-- If the right-whiskered filler triangles of two semantic 2-cells compare by a
3-cell, then their normalized explicit right-whisker shells also compare. -/
noncomputable def reductionSeq_whiskerRightCongrOfTriangleComparisonPath3_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M}
    {η θ : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)}
    (s : ReductionSeq M N)
    (triangleComparison :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
              (η ρ) ((reductionSeq_in_Theory1 K s) ρ))
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
              (θ ρ) ((reductionSeq_in_Theory1 K s) ρ)))
        (Theory2.refl K
          (Theory1.comp K
            (reductionSeq_in_Theory1 K p)
            (reductionSeq_in_Theory1 K s)))) :
    Theory3 K
      (reductionSeq_whiskerRight_in_Theory2 K η s)
      (reductionSeq_whiskerRight_in_Theory2 K θ s) :=
  reductionSeq_whiskerRightCongr_in_Theory3 K s
    (Theory3.whiskerRightCongrOfTriangleComparisonPath3 K
      (reductionSeq_in_Theory1 K s) triangleComparison)

/-- Interpreting structural right whiskering of a vertical composite agrees with
the composite of the interpreted structural right whiskers of the factors. -/
noncomputable def homotopy2_whiskerRightTrans_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q r : ReductionSeq L M}
    (α : Homotopy2 p q) (β : Homotopy2 q r) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (whiskerRight (Homotopy2.trans α β) s))
      (Theory2.trans K
        (homotopy2_in_Theory2 K (whiskerRight α s))
        (homotopy2_in_Theory2 K (whiskerRight β s))) := by
  let η := homotopy2_in_Theory2 K α
  let θ := homotopy2_in_Theory2 K β
  let shellη := reductionSeq_whiskerRight_in_Theory2 K η s
  let shellθ := reductionSeq_whiskerRight_in_Theory2 K θ s
  let directη := homotopy2_in_Theory2 K (whiskerRight α s)
  let directθ := homotopy2_in_Theory2 K (whiskerRight β s)
  exact Theory3.trans K
    (homotopy2_whiskerRight_bridge_in_Theory3 K (Homotopy2.trans α β) s)
    (Theory3.trans K
      (reductionSeq_whiskerRightTrans_in_Theory3 K η θ s)
      (Theory3.trans K
        (Theory3.transCongrLeft K
          (Theory3.symm K (homotopy2_whiskerRight_bridge_in_Theory3 K α s))
          shellθ)
      (Theory3.transCongrRight K directη
          (Theory3.symm K (homotopy2_whiskerRight_bridge_in_Theory3 K β s)))))

/-- Two-step vertical composition of equality-generated semantic 2-cells
contracts to the equality-generated semantic 2-cell on the composite endpoint
equality. -/
noncomputable def theory2_transOfEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N}
    (h₁ : α = β) (h₂ : β = γ) :
    Theory3 K
      (Theory2.trans K (Theory2.ofEq K h₁) (Theory2.ofEq K h₂))
      (Theory2.ofEq K (h₁.trans h₂)) := by
  cases h₁
  cases h₂
  simpa using (Theory3.transReflRight K (Theory2.refl K α))

/-- Left-associated three-step vertical composition of equality-generated
semantic 2-cells contracts to the equality-generated semantic 2-cell on the
composite endpoint equality. -/
noncomputable def theory2_transTransOfEq_toOfEq_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {α β γ δ : Theory1 K M N}
    (h₁ : α = β) (h₂ : β = γ) (h₃ : γ = δ) :
    Theory3 K
      (Theory2.trans K
        (Theory2.trans K (Theory2.ofEq K h₁) (Theory2.ofEq K h₂))
        (Theory2.ofEq K h₃))
      (Theory2.ofEq K ((h₁.trans h₂).trans h₃)) := by
  have hRightAssoc :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K (Theory2.ofEq K h₁) (Theory2.ofEq K h₂))
          (Theory2.ofEq K h₃))
        (Theory2.trans K
          (Theory2.ofEq K h₁)
          (Theory2.trans K (Theory2.ofEq K h₂) (Theory2.ofEq K h₃))) :=
    Theory3.transAssoc K (Theory2.ofEq K h₁) (Theory2.ofEq K h₂) (Theory2.ofEq K h₃)
  have hCollapseRight :
      Theory3 K
        (Theory2.trans K
          (Theory2.ofEq K h₁)
          (Theory2.trans K (Theory2.ofEq K h₂) (Theory2.ofEq K h₃)))
        (Theory2.trans K
          (Theory2.ofEq K h₁)
          (Theory2.ofEq K (h₂.trans h₃))) :=
    Theory3.transCongrRight K (Theory2.ofEq K h₁)
      (theory2_transOfEq_toOfEq_in_Theory3 K h₂ h₃)
  have hCollapseAll :
      Theory3 K
        (Theory2.trans K
          (Theory2.ofEq K h₁)
          (Theory2.ofEq K (h₂.trans h₃)))
        (Theory2.ofEq K (h₁.trans (h₂.trans h₃))) :=
    theory2_transOfEq_toOfEq_in_Theory3 K h₁ (h₂.trans h₃)
  have hOfEqProofs :
      Theory2.ofEq K (h₁.trans (h₂.trans h₃)) =
        Theory2.ofEq K ((h₁.trans h₂).trans h₃) := by
    exact congrArg (Theory2.ofEq K) (Subsingleton.elim _ _)
  exact Theory3.trans K hRightAssoc
    (Theory3.trans K hCollapseRight
      (Theory3.trans K hCollapseAll (Theory3.ofEq K hOfEqProofs)))

/-- In any extensional Kan complex the semantic image of the syntactic triangle
3-cell is a valid semantic 3-conversion.  The proof normalises the associator
and left-unitor interpretations to `Theory2.ofEq` forms, applies the existing
`reductionSeq_whiskerLeftRefl_in_Theory3` and `Theory3.transReflRight` to
eliminate the reflexive whisker, and then bridges the two `ofEq`-normal forms
using proof-irrelevance together with the preexisting target bridge
`homotopy2_triangle_target_ofEq_toOfEq_in_Theory3`. -/
noncomputable def homotopy2_triangle_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (Homotopy2.trans (HigherTerms.associator p (ReductionSeq.refl M) q)
          (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q))))
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerRight (HigherTerms.rightUnitor p) q)) := by
  -- Source unfolds definitionally to a trans of a whiskerLeft.
  change Theory3 K
    (Theory2.trans K
      (homotopy2_in_Theory2 K (HigherTerms.associator p (ReductionSeq.refl M) q))
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (homotopy2_in_Theory2 K (HigherTerms.leftUnitor q))))
    (homotopy2_in_Theory2 K
      (HigherTerms.whiskerRight (HigherTerms.rightUnitor p) q))
  -- Unfold associator and leftUnitor, then apply homotopy2_in_Theory2_ofEq.
  simp only [HigherTerms.associator, HigherTerms.leftUnitor, homotopy2_in_Theory2_ofEq]
  -- The leftUnitor gives congrArg _ (concat_refl_left q), which equals rfl
  -- by proof irrelevance (both prove reductionSeq_in_Theory1 K (concat ε q) = reductionSeq_in_Theory1 K q,
  -- and concat ε q = q definitionally).
  rw [show congrArg (fun r => reductionSeq_in_Theory1 K r) (ReductionSeq.concat_refl_left q) =
    rfl from Subsingleton.elim _ _]
  -- Now goal: Theory3 K (trans (ofEq A) (reductionSeq_whiskerLeft p (refl))) target.
  -- Chain: trans(ofEq A, wL p refl) → trans(ofEq A, refl) → ofEq A → ofEq D → target.
  exact Theory3.trans K
    (Theory3.trans K
      (Theory3.transCongrRight K _
        (reductionSeq_whiskerLeftRefl_in_Theory3 K p q))
      (Theory3.transReflRight K _))
    (Theory3.trans K
      (Theory3.ofEq K (congrArg (Theory2.ofEq K) (Subsingleton.elim _ _)))
      (Theory3.symm K (homotopy2_triangle_target_ofEq_toOfEq_in_Theory3 K p q)))

/-- The primitive triangle 3-cell contracts the structural source shell built
from the explicit associator equality and left-unitor shell to the
equality-generated right-whisker endpoint shell. This packages the triangle in
the exact structural-endpoint form needed by later shell comparisons. -/
noncomputable def homotopy2_triangle_shell_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.ofEq K
          (congrArg (fun r => reductionSeq_in_Theory1 K r)
            (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_leftUnitor_shell_in_Theory2 K q)))
      (Theory2.ofEq K
        (congrArg (fun r => reductionSeq_in_Theory1 K r)
          (congrArg (fun r => ReductionSeq.concat r q)
            (ReductionSeq.concat_refl_right p)))) := by
  exact Theory3.trans K
    (Theory3.symm K (homotopy2_triangle_source_shell_in_Theory3 K p q))
    (Theory3.trans K
      (homotopy2_triangle_in_Theory3 K p q)
      (homotopy2_triangle_target_ofEq_toOfEq_in_Theory3 K p q))

/-- In any extensional Kan complex the semantic image of the syntactic pentagon
3-cell is a valid semantic 3-conversion. The proof normalises both sides to a
single equality-generated semantic 2-cell, using the specialized whisker
bridges for the two whiskered associator factors and collapsing the resulting
left-associated composite of `Theory2.ofEq` witnesses by proof irrelevance. -/
noncomputable def homotopy2_pentagon_in_Theory3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (Homotopy2.trans
          (HigherTerms.associator (ReductionSeq.concat p q) r s)
          (HigherTerms.associator p q (ReductionSeq.concat r s))))
      (homotopy2_in_Theory2 K
        (Homotopy2.trans
          (Homotopy2.trans
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s)
            (HigherTerms.associator p (ReductionSeq.concat q r) s))
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s)))) := by
  let hSourceLeft :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (ReductionSeq.concat_assoc (ReductionSeq.concat p q) r s)
  let hSourceRight :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (ReductionSeq.concat_assoc p q (ReductionSeq.concat r s))
  let hRightWhisker :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (congrArg (fun u => ReductionSeq.concat u s)
        (ReductionSeq.concat_assoc p q r))
  let hMid :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (ReductionSeq.concat_assoc p (ReductionSeq.concat q r) s)
  let hLeftWhisker :=
    congrArg (fun u => reductionSeq_in_Theory1 K u)
      (congrArg (fun u => ReductionSeq.concat p u)
        (ReductionSeq.concat_assoc q r s))
  let hSource := hSourceLeft.trans hSourceRight
  let hTarget := (hRightWhisker.trans hMid).trans hLeftWhisker
  change Theory3 K
    (Theory2.trans K
      (homotopy2_in_Theory2 K
        (HigherTerms.associator (ReductionSeq.concat p q) r s))
      (homotopy2_in_Theory2 K
        (HigherTerms.associator p q (ReductionSeq.concat r s))))
    (Theory2.trans K
      (Theory2.trans K
        (homotopy2_in_Theory2 K
          (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
        (homotopy2_in_Theory2 K
          (HigherTerms.associator p (ReductionSeq.concat q r) s)))
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerLeft p (HigherTerms.associator q r s))))
  simp only [HigherTerms.associator, homotopy2_in_Theory2_ofEq]
  have hSourceToOfEq :
      Theory3 K
        (Theory2.trans K
          (Theory2.ofEq K hSourceLeft)
          (Theory2.ofEq K hSourceRight))
        (Theory2.ofEq K hSource) :=
    theory2_transOfEq_toOfEq_in_Theory3 K hSourceLeft hSourceRight
  have hTargetInner :
      Theory3 K
        (Theory2.trans K
          (homotopy2_in_Theory2 K
            (HigherTerms.whiskerRight (HigherTerms.Homotopy2.ofEq
              (ReductionSeq.concat_assoc p q r)) s))
          (Theory2.ofEq K hMid))
        (Theory2.trans K
          (Theory2.ofEq K hRightWhisker)
          (Theory2.ofEq K hMid)) :=
    Theory3.transCongrLeft K
      (homotopy2_pentagon_rightWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3
        K p q r s)
      (Theory2.ofEq K hMid)
  have hTargetNormalize :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (homotopy2_in_Theory2 K
              (HigherTerms.whiskerRight (HigherTerms.Homotopy2.ofEq
                (ReductionSeq.concat_assoc p q r)) s))
            (Theory2.ofEq K hMid))
          (homotopy2_in_Theory2 K
            (HigherTerms.whiskerLeft p (HigherTerms.Homotopy2.ofEq
              (ReductionSeq.concat_assoc q r s)))))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.ofEq K hRightWhisker)
            (Theory2.ofEq K hMid))
          (Theory2.ofEq K hLeftWhisker)) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K
        (Theory2.trans K
          (homotopy2_in_Theory2 K
            (HigherTerms.whiskerRight (HigherTerms.Homotopy2.ofEq
              (ReductionSeq.concat_assoc p q r)) s))
          (Theory2.ofEq K hMid))
        (homotopy2_pentagon_leftWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3
          K p q r s))
      (Theory3.transCongrLeft K hTargetInner
        (Theory2.ofEq K hLeftWhisker))
  have hTargetToOfEq :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (homotopy2_in_Theory2 K
              (HigherTerms.whiskerRight (HigherTerms.Homotopy2.ofEq
                (ReductionSeq.concat_assoc p q r)) s))
            (Theory2.ofEq K hMid))
          (homotopy2_in_Theory2 K
            (HigherTerms.whiskerLeft p (HigherTerms.Homotopy2.ofEq
              (ReductionSeq.concat_assoc q r s)))))
        (Theory2.ofEq K hTarget) := by
    exact Theory3.trans K hTargetNormalize
      (theory2_transTransOfEq_toOfEq_in_Theory3
        K hRightWhisker hMid hLeftWhisker)
  have hOfEqProofs :
      Theory2.ofEq K hSource = Theory2.ofEq K hTarget := by
    exact congrArg (Theory2.ofEq K) (Subsingleton.elim hSource hTarget)
  exact Theory3.trans K hSourceToOfEq
    (Theory3.trans K
      (Theory3.ofEq K hOfEqProofs)
      (Theory3.symm K hTargetToOfEq))

/-- If associator 2-cells already bridge to their structural shells, then left
whiskering preserves that bridge at the semantic level. This packages the
left-whiskered associator factor used in pentagon endpoint comparisons. -/
noncomputable def homotopy2_whiskerLeft_associator_bridge_in_Theory3_of_associatorBridge
    (K : ExtensionalKanComplex)
    (hAssocBridge :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
          (reductionSeq_associator_shell_in_Theory2 K p q r))
    {A B C D E : Term}
    (p : ReductionSeq A B)
    (q : ReductionSeq B C) (r : ReductionSeq C D) (s : ReductionSeq D E) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerLeft p (HigherTerms.associator q r s)))
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K q r s)) := by
  change Theory3 K
    (reductionSeq_whiskerLeft_in_Theory2 K p
      (homotopy2_in_Theory2 K (HigherTerms.associator q r s)))
    (reductionSeq_whiskerLeft_in_Theory2 K p
      (reductionSeq_associator_shell_in_Theory2 K q r s))
  exact reductionSeq_whiskerLeftCongr_in_Theory3 K p
    (hAssocBridge q r s)

/-- Any associator-shell bridge upgrades the source endpoint of the explicit
pentagon 3-cell to the corresponding structural associator shells. -/
noncomputable def homotopy2_pentagon_source_bridge_in_Theory3_of_associatorBridge
    (K : ExtensionalKanComplex)
    (hAssocBridge :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
          (reductionSeq_associator_shell_in_Theory2 K p q r))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (Homotopy2.trans
          (HigherTerms.associator (ReductionSeq.concat p q) r s)
          (HigherTerms.associator p q (ReductionSeq.concat r s))))
      (Theory2.trans K
        (reductionSeq_associator_shell_in_Theory2 K
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K
          p q (ReductionSeq.concat r s))) := by
  have hLeft :
      Theory3 K
        (homotopy2_in_Theory2 K
          (HigherTerms.associator (ReductionSeq.concat p q) r s))
        (reductionSeq_associator_shell_in_Theory2 K
          (ReductionSeq.concat p q) r s) :=
    hAssocBridge (ReductionSeq.concat p q) r s
  have hRight :
      Theory3 K
        (homotopy2_in_Theory2 K
          (HigherTerms.associator p q (ReductionSeq.concat r s)))
        (reductionSeq_associator_shell_in_Theory2 K
          p q (ReductionSeq.concat r s)) :=
    hAssocBridge p q (ReductionSeq.concat r s)
  change Theory3 K
    (Theory2.trans K
      (homotopy2_in_Theory2 K
        (HigherTerms.associator (ReductionSeq.concat p q) r s))
      (homotopy2_in_Theory2 K
        (HigherTerms.associator p q (ReductionSeq.concat r s))))
    (Theory2.trans K
      (reductionSeq_associator_shell_in_Theory2 K
        (ReductionSeq.concat p q) r s)
      (reductionSeq_associator_shell_in_Theory2 K
        p q (ReductionSeq.concat r s)))
  exact Theory3.trans K
    (Theory3.transCongrRight K
      (homotopy2_in_Theory2 K
        (HigherTerms.associator (ReductionSeq.concat p q) r s))
      hRight)
    (Theory3.transCongrLeft K hLeft
      (reductionSeq_associator_shell_in_Theory2 K
        p q (ReductionSeq.concat r s)))

/-- Any associator-shell bridge also upgrades the target endpoint of the
explicit pentagon 3-cell to the mixed shell where only the right-whiskered
associator factor remains equality-generated. -/
noncomputable def homotopy2_pentagon_target_bridge_in_Theory3_of_associatorBridge
    (K : ExtensionalKanComplex)
    (hAssocBridge :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
          (reductionSeq_associator_shell_in_Theory2 K p q r))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (homotopy2_in_Theory2 K
        (Homotopy2.trans
          (Homotopy2.trans
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s)
            (HigherTerms.associator p (ReductionSeq.concat q r) s))
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s))))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.ofEq K
            (congrArg (fun u => reductionSeq_in_Theory1 K u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_associator_shell_in_Theory2 K q r s))) := by
  have hRight :
      Theory3 K
        (homotopy2_in_Theory2 K
          (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
        (Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (congrArg (fun u => ReductionSeq.concat u s)
              (ReductionSeq.concat_assoc p q r)))) :=
    homotopy2_pentagon_rightWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3
      K p q r s
  have hMid :
      Theory3 K
        (homotopy2_in_Theory2 K
          (HigherTerms.associator p (ReductionSeq.concat q r) s))
        (reductionSeq_associator_shell_in_Theory2 K
          p (ReductionSeq.concat q r) s) :=
    hAssocBridge p (ReductionSeq.concat q r) s
  have hLeft :
      Theory3 K
        (homotopy2_in_Theory2 K
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s)))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_associator_shell_in_Theory2 K q r s)) :=
    homotopy2_whiskerLeft_associator_bridge_in_Theory3_of_associatorBridge
      K hAssocBridge p q r s
  have hInner :
      Theory3 K
        (Theory2.trans K
          (homotopy2_in_Theory2 K
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
          (homotopy2_in_Theory2 K
            (HigherTerms.associator p (ReductionSeq.concat q r) s)))
        (Theory2.trans K
          (Theory2.ofEq K
            (congrArg (fun u => reductionSeq_in_Theory1 K u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K
            p (ReductionSeq.concat q r) s)) := by
    exact Theory3.trans K
      (Theory3.transCongrRight K
        (homotopy2_in_Theory2 K
          (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
        hMid)
      (Theory3.transCongrLeft K hRight
        (reductionSeq_associator_shell_in_Theory2 K
          p (ReductionSeq.concat q r) s))
  change Theory3 K
    (Theory2.trans K
      (Theory2.trans K
        (homotopy2_in_Theory2 K
          (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
        (homotopy2_in_Theory2 K
          (HigherTerms.associator p (ReductionSeq.concat q r) s)))
      (homotopy2_in_Theory2 K
        (HigherTerms.whiskerLeft p (HigherTerms.associator q r s))))
    (Theory2.trans K
      (Theory2.trans K
        (Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (congrArg (fun u => ReductionSeq.concat u s)
              (ReductionSeq.concat_assoc p q r))))
        (reductionSeq_associator_shell_in_Theory2 K
          p (ReductionSeq.concat q r) s))
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K q r s)))
  exact Theory3.trans K
    (Theory3.transCongrRight K
      (Theory2.trans K
        (homotopy2_in_Theory2 K
          (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
        (homotopy2_in_Theory2 K
          (HigherTerms.associator p (ReductionSeq.concat q r) s)))
      hLeft)
    (Theory3.transCongrLeft K hInner
      (reductionSeq_whiskerLeft_in_Theory2 K p
        (reductionSeq_associator_shell_in_Theory2 K q r s)))

/-- Combining the explicit pentagon 3-cell with an associator-shell bridge
identifies the structural source shell with the mixed target shell. This makes
the remaining pentagon debt explicit: only the right-whiskered factor stays in
equality-generated form. -/
noncomputable def homotopy2_pentagon_shell_bridge_in_Theory3_of_associatorBridge
    (K : ExtensionalKanComplex)
    (hAssocBridge :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
          (reductionSeq_associator_shell_in_Theory2 K p q r))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_associator_shell_in_Theory2 K
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.ofEq K
            (congrArg (fun u => reductionSeq_in_Theory1 K u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_associator_shell_in_Theory2 K q r s))) := by
  exact Theory3.trans K
    (Theory3.symm K
      (homotopy2_pentagon_source_bridge_in_Theory3_of_associatorBridge
        K hAssocBridge p q r s))
    (Theory3.trans K
      (homotopy2_pentagon_in_Theory3 K p q r s)
      (homotopy2_pentagon_target_bridge_in_Theory3_of_associatorBridge
        K hAssocBridge p q r s))

/-- If the right-whiskered filler triangles of the interpreted associator and
its structural shell compare, then the remaining equality-generated
right-whiskered associator factor upgrades to the structural right-whisker
shell. -/
noncomputable def homotopy2_pentagon_rightWhiskeredAssociator_shell_bridge_in_Theory3_ofTriangleComparisonPath3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q)
    (triangleComparison :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
              ((homotopy2_in_Theory2 K (HigherTerms.associator p q r)) ρ)
              ((reductionSeq_in_Theory1 K s) ρ))
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
              ((reductionSeq_associator_shell_in_Theory2 K p q r) ρ)
              ((reductionSeq_in_Theory1 K s) ρ)))
        (Theory2.refl K
          (Theory1.comp K
            (reductionSeq_in_Theory1 K
              (ReductionSeq.concat (ReductionSeq.concat p q) r))
            (reductionSeq_in_Theory1 K s)))) :
    Theory3 K
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (congrArg (fun u => ReductionSeq.concat u s)
            (ReductionSeq.concat_assoc p q r))))
      (reductionSeq_whiskerRight_in_Theory2 K
        (reductionSeq_associator_shell_in_Theory2 K p q r) s) := by
  let η := homotopy2_in_Theory2 K (HigherTerms.associator p q r)
  let θ := reductionSeq_associator_shell_in_Theory2 K p q r
  have hOfEqToInterp :
      Theory3 K
        (Theory2.ofEq K
          (congrArg (fun u => reductionSeq_in_Theory1 K u)
            (congrArg (fun u => ReductionSeq.concat u s)
              (ReductionSeq.concat_assoc p q r))))
        (reductionSeq_whiskerRight_in_Theory2 K η s) := by
    exact Theory3.trans K
      (Theory3.symm K
        (homotopy2_pentagon_rightWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3
          K p q r s))
      (homotopy2_whiskerRight_bridge_in_Theory3 K
        (HigherTerms.associator p q r) s)
  have hInterpToShell :
      Theory3 K
        (reductionSeq_whiskerRight_in_Theory2 K η s)
        (reductionSeq_whiskerRight_in_Theory2 K θ s) :=
    reductionSeq_whiskerRightCongrOfTriangleComparisonPath3_in_Theory3 K s
      triangleComparison
  exact Theory3.trans K hOfEqToInterp hInterpToShell

/-- If the remaining equality-generated right-whiskered associator factor can be
upgraded to the structural right-whisker shell, then the whole explicit
pentagon shell upgrades to a fully structural target shell. This isolates the
last missing ingredient in the pentagon promotion story. -/
noncomputable def homotopy2_pentagon_structural_shell_bridge_in_Theory3_of_associatorRightWhiskerBridges
    (K : ExtensionalKanComplex)
    (hAssocBridge :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
          (reductionSeq_associator_shell_in_Theory2 K p q r))
    (hRightBridge :
      {L M N P Q : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) → (s : ReductionSeq P Q) →
        Theory3 K
          (Theory2.ofEq K
            (congrArg (fun u => reductionSeq_in_Theory1 K u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_whiskerRight_in_Theory2 K
            (reductionSeq_associator_shell_in_Theory2 K p q r) s))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_associator_shell_in_Theory2 K
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K
        (Theory2.trans K
          (reductionSeq_whiskerRight_in_Theory2 K
            (reductionSeq_associator_shell_in_Theory2 K p q r) s)
          (reductionSeq_associator_shell_in_Theory2 K
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_associator_shell_in_Theory2 K q r s))) := by
  let shellMid := reductionSeq_associator_shell_in_Theory2 K
    p (ReductionSeq.concat q r) s
  let shellLeft := reductionSeq_whiskerLeft_in_Theory2 K p
    (reductionSeq_associator_shell_in_Theory2 K q r s)
  have hInner :
      Theory3 K
        (Theory2.trans K
          (Theory2.ofEq K
            (congrArg (fun u => reductionSeq_in_Theory1 K u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          shellMid)
        (Theory2.trans K
          (reductionSeq_whiskerRight_in_Theory2 K
            (reductionSeq_associator_shell_in_Theory2 K p q r) s)
          shellMid) :=
    Theory3.transCongrLeft K (hRightBridge p q r s) shellMid
  have hTargetUpgrade :
      Theory3 K
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.ofEq K
              (congrArg (fun u => reductionSeq_in_Theory1 K u)
                (congrArg (fun u => ReductionSeq.concat u s)
                  (ReductionSeq.concat_assoc p q r))))
            shellMid)
          shellLeft)
        (Theory2.trans K
          (Theory2.trans K
            (reductionSeq_whiskerRight_in_Theory2 K
              (reductionSeq_associator_shell_in_Theory2 K p q r) s)
            shellMid)
          shellLeft) :=
    Theory3.transCongrLeft K hInner shellLeft
  exact Theory3.trans K
    (homotopy2_pentagon_shell_bridge_in_Theory3_of_associatorBridge
      K hAssocBridge p q r s)
    hTargetUpgrade

/-- A family of right-whiskered associator triangle comparisons is enough to
upgrade the explicit pentagon shell all the way to the fully structural target
shell, provided associators themselves already bridge to their structural
shells. -/
noncomputable def homotopy2_pentagon_structural_shell_bridge_in_Theory3_of_associatorBridgeOfTriangleComparisonPath3
    (K : ExtensionalKanComplex)
    (hAssocBridge :
      {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) →
        Theory3 K
          (homotopy2_in_Theory2 K (HigherTerms.associator p q r))
          (reductionSeq_associator_shell_in_Theory2 K p q r))
    (hAssocTriangle :
      {L M N P Q : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) → (s : ReductionSeq P Q) →
        Theory3 K
          (fun ρ =>
            K.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
                ((homotopy2_in_Theory2 K (HigherTerms.associator p q r)) ρ)
                ((reductionSeq_in_Theory1 K s) ρ))
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
                ((reductionSeq_associator_shell_in_Theory2 K p q r) ρ)
                ((reductionSeq_in_Theory1 K s) ρ)))
          (Theory2.refl K
            (Theory1.comp K
              (reductionSeq_in_Theory1 K
                (ReductionSeq.concat (ReductionSeq.concat p q) r))
              (reductionSeq_in_Theory1 K s))))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_associator_shell_in_Theory2 K
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K
        (Theory2.trans K
          (reductionSeq_whiskerRight_in_Theory2 K
            (reductionSeq_associator_shell_in_Theory2 K p q r) s)
          (reductionSeq_associator_shell_in_Theory2 K
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K p
          (reductionSeq_associator_shell_in_Theory2 K q r s))) := by
  exact homotopy2_pentagon_structural_shell_bridge_in_Theory3_of_associatorRightWhiskerBridges
    K hAssocBridge
    (fun {_ _ _ _ _} p q r s =>
      homotopy2_pentagon_rightWhiskeredAssociator_shell_bridge_in_Theory3_ofTriangleComparisonPath3
        K p q r s (hAssocTriangle p q r s))
    p q r s

/-- Every structurally supported syntactic 3-cell between parallel explicit
2-cells induces a semantic 3-conversion between the corresponding interpreted
semantic 2-cells in a fixed extensional Kan complex. -/
noncomputable def structuralHomotopy3_in_Theory3
    (K : ExtensionalKanComplex) :
    {M N : Term} → {p q : ReductionSeq M N} → {α β : Homotopy2 p q} →
      HigherLambdaModel.Lambda.HigherTerms.StructuralHomotopy3 α β →
        Theory3 K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)
  | _, _, _, _, _, _, .refl α =>
      homotopy2_refl_in_Theory3 K α
  | _, _, _, _, _, _, .ofEq h =>
      homotopy2_eq_in_Theory3 K h
  | _, _, _, _, _, _, .symm η =>
      Theory3.symm K (structuralHomotopy3_in_Theory3 K η)
  | _, _, _, _, _, _, .trans η θ =>
      Theory3.trans K
        (structuralHomotopy3_in_Theory3 K η)
        (structuralHomotopy3_in_Theory3 K θ)
  | _, _, _, _, _, _, .transCongrLeft η θ =>
      Theory3.transCongrLeft K
        (structuralHomotopy3_in_Theory3 K η)
        (homotopy2_in_Theory2 K θ)
  | _, _, _, _, _, _, .transCongrRight η θ =>
      Theory3.transCongrRight K
        (homotopy2_in_Theory2 K η)
        (structuralHomotopy3_in_Theory3 K θ)
  | _, _, _, _, _, _, .whiskerLeftCongr r η =>
      reductionSeq_whiskerLeftCongr_in_Theory3 K r
        (structuralHomotopy3_in_Theory3 K η)
  | _, _, _, _, _, _, .whiskerLeftRefl r p =>
      reductionSeq_whiskerLeftRefl_in_Theory3 K r p
  | _, _, _, _, _, _, .whiskerLeftTrans r α β =>
      reductionSeq_whiskerLeftTrans_in_Theory3 K r
        (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)
  | _, _, _, _, _, _, .whiskerLeftSymm r α =>
      reductionSeq_whiskerLeftSymm_in_Theory3 K r (homotopy2_in_Theory2 K α)
  | _, _, _, _, _, _, .invWhiskerLeft r α =>
      Theory3.symm K
        (reductionSeq_whiskerLeftSymm_in_Theory3 K r (homotopy2_in_Theory2 K α))
  | _, _, _, _, _, _, .whiskerRightRefl p s =>
      homotopy2_refl_in_Theory3 K (Homotopy2.refl (ReductionSeq.concat p s))
  | _, _, _, _, _, _, .whiskerRightTrans α β s =>
      homotopy2_whiskerRightTrans_bridge_in_Theory3 K α β s
  | _, _, _, _, _, _, .whiskerRightSymm α s =>
      Theory3.trans K
        (homotopy2_whiskerRight_bridge_in_Theory3 K (Homotopy2.symm α) s)
        (Theory3.trans K
          (reductionSeq_whiskerRightSymm_in_Theory3 K
            (homotopy2_in_Theory2 K α) s)
          (Theory3.symmCongr K
            (Theory3.symm K
              (homotopy2_whiskerRight_bridge_in_Theory3 K α s))))
  | _, _, _, _, _, _, .invWhiskerRight α s =>
      Theory3.trans K
        (Theory3.symmCongr K
          (homotopy2_whiskerRight_bridge_in_Theory3 K α s))
        (Theory3.trans K
          (Theory3.symm K
              (reductionSeq_whiskerRightSymm_in_Theory3 K
                (homotopy2_in_Theory2 K α) s))
          (Theory3.symm K
            (homotopy2_whiskerRight_bridge_in_Theory3 K (Homotopy2.symm α) s)))
  | _, _, _, _, _, _, .interchange α β =>
      homotopy2_eq_in_Theory3 K rfl
  | _, _, _, _, _, _, .interchange' α β =>
      homotopy2_interchange'_bridge_in_Theory3 K α β
  | _, _, _, _, _, _, .pentagon p q r s =>
      homotopy2_pentagon_in_Theory3 K p q r s
  | _, _, _, _, _, _, .triangle p q =>
      homotopy2_triangle_in_Theory3 K p q

/-- Every structurally supported syntactic 2-cell between explicit βη paths
induces a semantic 2-conversion between the corresponding structural semantic
1-cells in a fixed model. -/
noncomputable def structuralHomotopy2_in_Theory2
    (K : ExtensionalKanComplex) :
    {M N : Term} → {p q : ReductionSeq M N} →
      StructuralHomotopy2 p q →
        Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)
  | _, _, _, _, .refl p => reductionSeq_refl_in_Theory2 K p
  | _, _, _, _, .ofEq h =>
      Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h)
  | _, _, _, _, .symm α =>
      reductionSeq_symm_in_Theory2 K (structuralHomotopy2_in_Theory2 K α)
  | _, _, _, _, .trans α β =>
      Theory2.trans K
        (structuralHomotopy2_in_Theory2 K α)
        (structuralHomotopy2_in_Theory2 K β)
  | _, _, _, _, .whiskerLeft r α =>
      reductionSeq_whiskerLeft_in_Theory2 K r
        (structuralHomotopy2_in_Theory2 K α)
  | _, _, _, _, .whiskerRight (.refl p) s =>
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))
  | _, _, _, _, .whiskerRight α s =>
      reductionSeq_whiskerRight_in_Theory2 K
        (structuralHomotopy2_in_Theory2 K α) s

/-- Equality-generated HoTFT 1-conversion associated to an explicit βη path.
This auxiliary bridge is used internally to compare the structural HoTFT
interpretation with the underlying equality semantics. -/
noncomputable def reductionSeq_eq_in_HoTFT1 {M N : Term} (p : ReductionSeq M N) :
    HoTFT1 M N :=
  HoTFT1.ofHoTFTEq (reductionSeq_in_HoTFT p)

/-- Any two parallel explicit βη paths induce the same equality-generated
proof-relevant HoTFT 1-conversion. -/
theorem reductionSeq_eq_in_HoTFT1_eq {M N : Term} (p q : ReductionSeq M N) :
    reductionSeq_eq_in_HoTFT1 p = reductionSeq_eq_in_HoTFT1 q := by
  unfold reductionSeq_eq_in_HoTFT1
  have hproof : reductionSeq_in_HoTFT p = reductionSeq_in_HoTFT q :=
    Subsingleton.elim _ _
  exact congrArg HoTFT1.ofHoTFTEq hproof

/-- Every explicit βη path is structurally homotopic to its equality-generated
HoTFT interpretation. -/
noncomputable def reductionSeq_in_eq_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_eq_in_HoTFT1 p) :=
  fun K => reductionSeq_in_eq_in_Theory2 K p

/-- Structural left whiskering of a semantic HoTFT 2-cell along an explicit βη
path. -/
noncomputable def reductionSeq_whiskerLeft_in_HoTFT2
    {L M N : Term} (r : ReductionSeq L M) {p q : ReductionSeq M N} :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) →
      HoTFT2 (reductionSeq_in_HoTFT1 (ReductionSeq.concat r p))
        (reductionSeq_in_HoTFT1 (ReductionSeq.concat r q))
  | η => fun K => reductionSeq_whiskerLeft_in_Theory2 K r (η K)

/-- Structural left whiskering along an explicit βη path is congruent on HoTFT
3-cells. -/
noncomputable def reductionSeq_whiskerLeftCongr_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) {p q : ReductionSeq M N}
    {η θ : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)}
    (Κ : HoTFT3 η θ) :
    HoTFT3 (reductionSeq_whiskerLeft_in_HoTFT2 r η)
      (reductionSeq_whiskerLeft_in_HoTFT2 r θ) :=
  fun K => reductionSeq_whiskerLeftCongr_in_Theory3 K r (Κ K)

/-- Structural left whiskering along an explicit βη path commutes with vertical
composition up to proof-relevant HoTFT 3-cells. -/
noncomputable def reductionSeq_whiskerLeftTrans_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) {p q s : ReductionSeq M N}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (θ : HoTFT2 (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 s)) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 r (HoTFT2.trans η θ))
      (HoTFT2.trans (reductionSeq_whiskerLeft_in_HoTFT2 r η)
        (reductionSeq_whiskerLeft_in_HoTFT2 r θ)) :=
  fun K => reductionSeq_whiskerLeftTrans_in_Theory3 K r (η K) (θ K)

/-- Structural left whiskering along an explicit βη path commutes with symmetry
up to proof-relevant HoTFT 3-cells. -/
noncomputable def reductionSeq_whiskerLeftSymm_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) {p q : ReductionSeq M N}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 r (HoTFT2.symm η))
      (HoTFT2.symm (reductionSeq_whiskerLeft_in_HoTFT2 r η)) :=
  fun K => reductionSeq_whiskerLeftSymm_in_Theory3 K r (η K)

/-- Structural comparison between semantic composition of the HoTFT 1-cells
induced by explicit βη paths and interpretation of their syntactic
concatenation. -/
noncomputable def reductionSeq_comp_in_HoTFT2
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
      (reductionSeq_in_HoTFT1 (ReductionSeq.concat p q)) :=
  fun K => reductionSeq_comp_in_Theory2 K p q

/-- Generic structural right whiskering of a semantic HoTFT 2-cell along an
explicit βη path.

The structural and full HoTFT interpreters special-case reflexive input and use
the normalized semantic whisker directly. This helper remains the generic shell
for non-reflexive right whiskering. -/
noncomputable def reductionSeq_whiskerRight_in_HoTFT2
    {L M N : Term} {p q : ReductionSeq L M}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (s : ReductionSeq M N) :
    HoTFT2 (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))
      (reductionSeq_in_HoTFT1 (ReductionSeq.concat q s)) :=
  HoTFT2.trans (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 p s))
    (HoTFT2.trans
      (HoTFT2.whiskerRight η (reductionSeq_in_HoTFT1 s))
      (reductionSeq_comp_in_HoTFT2 q s))

/-- Reflexivity of the structural HoTFT 2-cell associated to an explicit βη
path. -/
noncomputable def reductionSeq_refl_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.refl (reductionSeq_in_HoTFT1 p)

/-- Associator for semantic composition of the structural HoTFT 1-cells
induced by explicit βη paths. -/
noncomputable def reductionSeq_associator_in_HoTFT2
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT2
      (HoTFT1.comp
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
        (reductionSeq_in_HoTFT1 r))
      (HoTFT1.comp
        (reductionSeq_in_HoTFT1 p)
        (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))) :=
  HoTFT2.associator (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)
    (reductionSeq_in_HoTFT1 r)

/-- Right inverse law for the structural HoTFT 1-cell induced by an explicit
βη path. -/
noncomputable def reductionSeq_rightInverse_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_inv_in_HoTFT1 p))
      (HoTFT1.refl M) :=
  HoTFT2.rightInverse (reductionSeq_in_HoTFT1 p)

/-- Left inverse law for the structural HoTFT 1-cell induced by an explicit
βη path. -/
noncomputable def reductionSeq_leftInverse_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_inv_in_HoTFT1 p) (reductionSeq_in_HoTFT1 p))
      (HoTFT1.refl N) :=
  HoTFT2.leftInverse (reductionSeq_in_HoTFT1 p)

/-- Symmetry of the structural HoTFT 2-cell associated to explicit βη paths. -/
noncomputable def reductionSeq_symm_in_HoTFT2
    {M N : Term} {p q : ReductionSeq M N} :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) →
      HoTFT2 (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 p)
  | η => HoTFT2.symm η

/-- Left unitor for the structural HoTFT 1-cell associated to an explicit βη
path. -/
noncomputable def reductionSeq_leftUnitor_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (HoTFT1.refl M) (reductionSeq_in_HoTFT1 p))
      (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.leftUnitor (reductionSeq_in_HoTFT1 p)

/-- Right unitor for the structural HoTFT 1-cell associated to an explicit βη
path. -/
noncomputable def reductionSeq_rightUnitor_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (HoTFT1.refl N))
      (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.rightUnitor (reductionSeq_in_HoTFT1 p)

/-- HoTFT counterpart of `reductionSeq_rightUnitor_shell_in_Theory2`. -/
noncomputable def reductionSeq_rightUnitor_shell_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (reductionSeq_in_HoTFT1 (ReductionSeq.concat p (ReductionSeq.refl N)))
      (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.trans
    (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 p (ReductionSeq.refl N)))
    (reductionSeq_rightUnitor_in_HoTFT2 p)

/-- HoTFT counterpart of `reductionSeq_leftUnitor_shell_in_Theory2`. -/
noncomputable def reductionSeq_leftUnitor_shell_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (reductionSeq_in_HoTFT1 (ReductionSeq.concat (ReductionSeq.refl M) p))
      (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.trans
    (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 (ReductionSeq.refl M) p))
    (reductionSeq_leftUnitor_in_HoTFT2 p)

/-- HoTFT counterpart of `reductionSeq_associator_shell_in_Theory2`. -/
noncomputable def reductionSeq_associator_source_in_HoTFT2
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT2
      (reductionSeq_in_HoTFT1
        (ReductionSeq.concat (ReductionSeq.concat p q) r))
      (HoTFT1.comp
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
        (reductionSeq_in_HoTFT1 r)) :=
  HoTFT2.trans
    (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 (ReductionSeq.concat p q) r))
    (HoTFT2.whiskerRight
      (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 p q))
      (reductionSeq_in_HoTFT1 r))

/-- HoTFT counterpart of `reductionSeq_associator_target_in_Theory2`. -/
noncomputable def reductionSeq_associator_target_in_HoTFT2
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT2
      (HoTFT1.comp
        (reductionSeq_in_HoTFT1 p)
        (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)))
      (reductionSeq_in_HoTFT1
        (ReductionSeq.concat p (ReductionSeq.concat q r))) :=
  HoTFT2.trans
    (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p)
      (reductionSeq_comp_in_HoTFT2 q r))
    (reductionSeq_comp_in_HoTFT2 p (ReductionSeq.concat q r))

/-- HoTFT counterpart of `reductionSeq_associator_shell_in_Theory2`. -/
noncomputable def reductionSeq_associator_shell_in_HoTFT2
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT2
      (reductionSeq_in_HoTFT1
        (ReductionSeq.concat (ReductionSeq.concat p q) r))
      (reductionSeq_in_HoTFT1
        (ReductionSeq.concat p (ReductionSeq.concat q r))) :=
  HoTFT2.trans
    (reductionSeq_associator_source_in_HoTFT2 p q r)
    (HoTFT2.trans
      (reductionSeq_associator_in_HoTFT2 p q r)
      (reductionSeq_associator_target_in_HoTFT2 p q r))

/-- HoTFT counterpart of `reductionSeq_leftUnitorComp_in_Theory3`. -/
noncomputable def reductionSeq_leftUnitorComp_in_HoTFT3
    {M N P : Term} (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator
          (HoTFT1.refl M)
          (reductionSeq_in_HoTFT1 q)
          (reductionSeq_in_HoTFT1 r))
        (HoTFT2.leftUnitor
          (HoTFT1.comp
            (reductionSeq_in_HoTFT1 q)
            (reductionSeq_in_HoTFT1 r))))
      (HoTFT2.whiskerRight
        (HoTFT2.leftUnitor (reductionSeq_in_HoTFT1 q))
        (reductionSeq_in_HoTFT1 r)) :=
  fun K => reductionSeq_leftUnitorComp_in_Theory3 K q r

/-- HoTFT counterpart of `reductionSeq_comp_leftUnitor_shell_in_Theory3`. -/
noncomputable def reductionSeq_comp_leftUnitor_shell_in_HoTFT3
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.trans
        (reductionSeq_comp_in_HoTFT2 (ReductionSeq.refl M) p)
        (reductionSeq_leftUnitor_shell_in_HoTFT2 p))
      (reductionSeq_leftUnitor_in_HoTFT2 p) :=
  fun K => reductionSeq_comp_leftUnitor_shell_in_Theory3 K p

/-- HoTFT counterpart of `reductionSeq_leftUnitorCompShell_in_Theory3`. -/
noncomputable def reductionSeq_leftUnitorCompShell_in_HoTFT3
    {M N P : Term} (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator
          (HoTFT1.refl M)
          (reductionSeq_in_HoTFT1 q)
          (reductionSeq_in_HoTFT1 r))
        (HoTFT2.trans
          (HoTFT2.whiskerLeft (HoTFT1.refl M)
            (reductionSeq_comp_in_HoTFT2 q r))
          (HoTFT2.trans
            (reductionSeq_comp_in_HoTFT2 (ReductionSeq.refl M)
              (ReductionSeq.concat q r))
            (reductionSeq_leftUnitor_shell_in_HoTFT2
              (ReductionSeq.concat q r)))))
      (HoTFT2.trans
        (HoTFT2.whiskerRight
          (HoTFT2.leftUnitor (reductionSeq_in_HoTFT1 q))
          (reductionSeq_in_HoTFT1 r))
        (reductionSeq_comp_in_HoTFT2 q r)) :=
  fun K => reductionSeq_leftUnitorCompShell_in_Theory3 K q r

/-- HoTFT counterpart of `reductionSeq_leftUnitorNaturality_in_Theory3`. -/
noncomputable def reductionSeq_leftUnitorNaturality_in_HoTFT3
    {M N P : Term} (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.whiskerLeft (HoTFT1.refl M)
          (reductionSeq_comp_in_HoTFT2 q r))
        (HoTFT2.leftUnitor
          (reductionSeq_in_HoTFT1 (ReductionSeq.concat q r))))
      (HoTFT2.trans
        (HoTFT2.leftUnitor
          (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)))
        (reductionSeq_comp_in_HoTFT2 q r)) :=
  fun K => reductionSeq_leftUnitorNaturality_in_Theory3 K q r

/-- HoTFT counterpart of `reductionSeq_comp_associator_refl_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_refl_in_HoTFT3
    {M N P : Term} (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.refl M) q r)
      (HoTFT2.ofEq
        (congrArg (fun t => reductionSeq_in_HoTFT1 t)
          (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r))) :=
  fun K => reductionSeq_comp_associator_refl_in_Theory3 K q r

/-- HoTFT counterpart of
`reductionSeq_comp_associator_refl_theoryWhiskerLeft_toOfEq_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_refl_theoryWhiskerLeft_toOfEq_in_HoTFT3
    {L M N P : Term}
    (α : HoTFT1 L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (HoTFT2.whiskerLeft α
        (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.refl M) q r))
      (HoTFT2.ofEq
        (congrArg (fun δ => HoTFT1.comp α δ)
          (congrArg (fun t => reductionSeq_in_HoTFT1 t)
            (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)))) :=
  fun K => reductionSeq_comp_associator_refl_theoryWhiskerLeft_toOfEq_in_Theory3 K (α K) q r

/-- HoTFT counterpart of
`reductionSeq_comp_associator_refl_theoryWhiskerLeft_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_refl_theoryWhiskerLeft_in_HoTFT3
    {L M N P : Term}
    (α : HoTFT1 L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (HoTFT2.whiskerLeft α
        (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.refl M) q r))
      (HoTFT2.refl
        (HoTFT1.comp α (reductionSeq_in_HoTFT1 (ReductionSeq.concat q r)))) :=
  fun K => reductionSeq_comp_associator_refl_theoryWhiskerLeft_in_Theory3 K (α K) q r

/-- HoTFT counterpart of
`reductionSeq_comp_associator_refl_semanticWhiskerLeft_toOfEq_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_refl_semanticWhiskerLeft_toOfEq_in_HoTFT3
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 p
        (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.refl M) q r))
      (HoTFT2.ofEq
        (congrArg (fun t => reductionSeq_in_HoTFT1 t)
          (congrArg (fun t => ReductionSeq.concat p t)
            (ReductionSeq.concat_assoc (ReductionSeq.refl M) q r)))) :=
  fun K => reductionSeq_comp_associator_refl_semanticWhiskerLeft_toOfEq_in_Theory3 K p q r

/-- HoTFT counterpart of
`reductionSeq_comp_associator_refl_semanticWhiskerLeft_in_Theory3`. -/
noncomputable def reductionSeq_comp_associator_refl_semanticWhiskerLeft_in_HoTFT3
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 p
        (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.refl M) q r))
      (HoTFT2.refl
        (reductionSeq_in_HoTFT1 (ReductionSeq.concat p (ReductionSeq.concat q r)))) :=
  fun K => reductionSeq_comp_associator_refl_semanticWhiskerLeft_in_Theory3 K p q r

/-- HoTFT counterpart of `reductionSeq_associator_target_step_in_Theory3`. -/
noncomputable def reductionSeq_associator_target_step_in_HoTFT3
    {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    HoTFT3
      (reductionSeq_associator_target_in_HoTFT2 (ReductionSeq.step s rest) q r)
      (HoTFT2.trans
        (HoTFT2.associator
          (betaEtaStep_in_HoTFT1 L M s)
          (reductionSeq_in_HoTFT1 rest)
          (HoTFT1.comp
            (reductionSeq_in_HoTFT1 q)
            (reductionSeq_in_HoTFT1 r)))
        (HoTFT2.whiskerLeft
          (betaEtaStep_in_HoTFT1 L M s)
          (reductionSeq_associator_target_in_HoTFT2 rest q r))) :=
  fun K => reductionSeq_associator_target_step_in_Theory3 K s rest q r

/-- HoTFT counterpart of `reductionSeq_associator_target_stepInv_in_Theory3`. -/
noncomputable def reductionSeq_associator_target_stepInv_in_HoTFT3
    {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    HoTFT3
      (reductionSeq_associator_target_in_HoTFT2 (ReductionSeq.stepInv s rest) q r)
      (HoTFT2.trans
        (HoTFT2.associator
          (betaEtaStepInv_in_HoTFT1 L M s)
          (reductionSeq_in_HoTFT1 rest)
          (HoTFT1.comp
            (reductionSeq_in_HoTFT1 q)
            (reductionSeq_in_HoTFT1 r)))
        (HoTFT2.whiskerLeft
          (betaEtaStepInv_in_HoTFT1 L M s)
          (reductionSeq_associator_target_in_HoTFT2 rest q r))) :=
  fun K => reductionSeq_associator_target_stepInv_in_Theory3 K s rest q r

/-- HoTFT counterpart of `reductionSeq_comp_associator_step_finish_in_Theory3`.
This packages the purely inductive bookkeeping once the step-head geometric
normalization has been proved at the HoTFT layer. -/
noncomputable def reductionSeq_comp_associator_step_finish_in_HoTFT3
    {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (ih :
      HoTFT3
        (reductionSeq_associator_shell_in_HoTFT2 rest q r)
        (HoTFT2.ofEq
          (congrArg (fun u => reductionSeq_in_HoTFT1 u)
            (ReductionSeq.concat_assoc rest q r))))
    (head :
      HoTFT3
        (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.step s rest) q r)
        (HoTFT2.whiskerLeft
          (betaEtaStep_in_HoTFT1 L M s)
          (reductionSeq_associator_shell_in_HoTFT2 rest q r))) :
    HoTFT3
      (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.step s rest) q r)
      (HoTFT2.ofEq
        (congrArg (fun u => reductionSeq_in_HoTFT1 u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s rest) q r))) := by
  let α : HoTFT1 L M := betaEtaStep_in_HoTFT1 L M s
  let hRest :=
    congrArg (fun u => reductionSeq_in_HoTFT1 u)
      (ReductionSeq.concat_assoc rest q r)
  exact HoTFT3.trans head
    (HoTFT3.whiskerLeftCongrOfEq α hRest ih)

/-- HoTFT counterpart of `reductionSeq_comp_associator_stepInv_finish_in_Theory3`.
This is the inverse-step bookkeeping analogue. -/
noncomputable def reductionSeq_comp_associator_stepInv_finish_in_HoTFT3
    {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q)
    (ih :
      HoTFT3
        (reductionSeq_associator_shell_in_HoTFT2 rest q r)
        (HoTFT2.ofEq
          (congrArg (fun u => reductionSeq_in_HoTFT1 u)
            (ReductionSeq.concat_assoc rest q r))))
    (head :
      HoTFT3
        (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.stepInv s rest) q r)
        (HoTFT2.whiskerLeft
          (betaEtaStepInv_in_HoTFT1 L M s)
          (reductionSeq_associator_shell_in_HoTFT2 rest q r))) :
    HoTFT3
      (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.stepInv s rest) q r)
      (HoTFT2.ofEq
        (congrArg (fun u => reductionSeq_in_HoTFT1 u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s rest) q r))) := by
  let α : HoTFT1 L M := betaEtaStepInv_in_HoTFT1 L M s
  let hRest :=
    congrArg (fun u => reductionSeq_in_HoTFT1 u)
      (ReductionSeq.concat_assoc rest q r)
  exact HoTFT3.trans head
    (HoTFT3.whiskerLeftCongrOfEq α hRest ih)

/-- HoTFT counterpart of `reductionSeq_comp_associator_in_Theory3_of_heads`.

The recursive bookkeeping is fully packaged here as well, leaving only the two
local head bridges to be supplied later. -/
noncomputable def reductionSeq_comp_associator_in_HoTFT3_of_heads
    (stepHead :
      ∀ {L M N P Q : Term} (s : BetaEtaStep L M) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        HoTFT3
          (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.step s rest) q r)
          (HoTFT2.whiskerLeft (betaEtaStep_in_HoTFT1 L M s)
            (reductionSeq_associator_shell_in_HoTFT2 rest q r)))
    (stepInvHead :
      ∀ {L M N P Q : Term} (s : BetaEtaStep M L) (rest : ReductionSeq M N)
          (q : ReductionSeq N P) (r : ReductionSeq P Q),
        HoTFT3
          (reductionSeq_associator_shell_in_HoTFT2 (ReductionSeq.stepInv s rest) q r)
          (HoTFT2.whiskerLeft (betaEtaStepInv_in_HoTFT1 L M s)
            (reductionSeq_associator_shell_in_HoTFT2 rest q r))) :
    {L M N P : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      (r : ReductionSeq N P) →
      HoTFT3
        (reductionSeq_associator_shell_in_HoTFT2 p q r)
        (HoTFT2.ofEq
          (congrArg (fun u => reductionSeq_in_HoTFT1 u)
            (ReductionSeq.concat_assoc p q r)))
  | _, _, _, _, .refl M, q, r =>
      reductionSeq_comp_associator_refl_in_HoTFT3 q r
  | _, _, _, _, .step s rest, q, r =>
      reductionSeq_comp_associator_step_finish_in_HoTFT3 s rest q r
        (reductionSeq_comp_associator_in_HoTFT3_of_heads stepHead stepInvHead rest q r)
        (stepHead s rest q r)
  | _, _, _, _, .stepInv s rest, q, r =>
      reductionSeq_comp_associator_stepInv_finish_in_HoTFT3 s rest q r
        (reductionSeq_comp_associator_in_HoTFT3_of_heads stepHead stepInvHead rest q r)
        (stepInvHead s rest q r)

/-- Degenerating the semantic composition triangle yields a boundary-aware
HoTFT tetrahedron whose middle face is the reflexive 2-cell on the semantic
composite path. -/
noncomputable def reductionSeq_comp_refl_in_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 q)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)) :=
  HoTFTTriangle.reflTetrahedron
    (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))

/-- The interpreted structural associator carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_associator_in_HoTFTTetrahedron
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle
        (HoTFT2.refl (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))))
      (HoTFT2.toTriangle (reductionSeq_associator_in_HoTFT2 p q r))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p)
        (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)))
      (HoTFT1.assocTriangle (reductionSeq_in_HoTFT1 p)
        (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)) :=
  HoTFT3.associatorTetrahedron
    (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)

/-- The interpreted structural left unitor carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_leftUnitor_in_HoTFTTetrahedron
    {M N : Term} (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT2.toTriangle (reductionSeq_leftUnitor_in_HoTFT2 p))
      (HoTFT1.sourceDegenerateTriangle (reductionSeq_in_HoTFT1 p))
      (HoTFT1.compTriangle (HoTFT1.refl M) (reductionSeq_in_HoTFT1 p)) :=
  HoTFT3.leftUnitorTetrahedron (reductionSeq_in_HoTFT1 p)

/-- The interpreted structural right unitor carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_rightUnitor_in_HoTFTTetrahedron
    {M N : Term} (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle (reductionSeq_rightUnitor_in_HoTFT2 p))
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (HoTFT1.refl N)) :=
  HoTFT3.rightUnitorTetrahedron (reductionSeq_in_HoTFT1 p)

/-- Every structurally supported syntactic 2-cell between explicit βη paths
induces a proof-relevant HoTFT 2-conversion between the corresponding
structural HoTFT 1-cells. -/
noncomputable def structuralHomotopy2_in_HoTFT2 :
    {M N : Term} → {p q : ReductionSeq M N} →
      StructuralHomotopy2 p q →
        HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)
  | _, _, _, _, .refl p => reductionSeq_refl_in_HoTFT2 p
  | _, _, _, _, .ofEq h =>
      HoTFT2.ofEq (congrArg (fun r => reductionSeq_in_HoTFT1 r) h)
  | _, _, _, _, .symm α =>
      reductionSeq_symm_in_HoTFT2 (structuralHomotopy2_in_HoTFT2 α)
  | _, _, _, _, .trans α β =>
      HoTFT2.trans (structuralHomotopy2_in_HoTFT2 α)
        (structuralHomotopy2_in_HoTFT2 β)
  | _, _, _, _, .whiskerLeft r α =>
      reductionSeq_whiskerLeft_in_HoTFT2 r (structuralHomotopy2_in_HoTFT2 α)
  | _, _, _, _, .whiskerRight (.refl p) s =>
      HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))
  | _, _, _, _, .whiskerRight α s =>
      reductionSeq_whiskerRight_in_HoTFT2
        (structuralHomotopy2_in_HoTFT2 α) s

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
proof-relevant HoTFT 2-conversion carried by actual semantic 2-simplices
between the corresponding structural HoTFT 1-cells. -/
noncomputable def homotopy2_in_HoTFT2 {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) :=
  fun K => homotopy2_in_Theory2 K α

/-- The interpreted structural vertical composition carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_trans_in_HoTFTTetrahedron
    {M N : Term} {p q s : ReductionSeq M N}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 β))
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 (Homotopy2.trans α β)))
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 α)) :=
  HoTFT3.transFillerTetrahedron
    (homotopy2_in_HoTFT2 α)
    (homotopy2_in_HoTFT2 β)

/-- Interpreting a syntactic reflexive 2-cell at the HoTFT layer is
definitionally the reflexive HoTFT 2-cell on the interpreted path. -/
theorem homotopy2_in_HoTFT2_ofEq
    {M N : Term} {p q : ReductionSeq M N} (h : p = q) :
    homotopy2_in_HoTFT2 (HigherTerms.Homotopy2.ofEq h) =
      HoTFT2.ofEq (congrArg (fun r => reductionSeq_in_HoTFT1 r) h) := by
  cases h
  rfl

/-- Interpreting a syntactic reflexive 2-cell at the HoTFT layer is
definitionally the reflexive HoTFT 2-cell on the interpreted path. -/
theorem homotopy2_in_HoTFT2_refl
    {M N : Term} (p : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (Homotopy2.refl p) =
      HoTFT2.refl (reductionSeq_in_HoTFT1 p) :=
  rfl

/-- Interpreting a reflexive syntactic right whisker at the HoTFT layer
unfolds definitionally to the reflexive HoTFT 2-cell on the interpreted
concatenation. -/
theorem homotopy2_in_HoTFT2_whiskerRight_refl
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (whiskerRight (Homotopy2.refl p) s) =
      HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s)) :=
  rfl

/-- Interpreting an equality-generated syntactic right whisker at the HoTFT
layer unfolds definitionally to the corresponding structural right-whisker
shell. -/
theorem homotopy2_in_HoTFT2_whiskerRight_ofEq
    {L M N : Term} {p q : ReductionSeq L M}
    (h : p = q) (s : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (whiskerRight (HigherTerms.Homotopy2.ofEq h) s) =
      reductionSeq_whiskerRight_in_HoTFT2
        (HoTFT2.ofEq (congrArg (fun r => reductionSeq_in_HoTFT1 r) h)) s :=
  by
    cases h
    rfl

/-- HoTFT 3-cell packaging the definitional bridge from the interpreted
syntactic `whiskerRight` reflexivity source to the reflexive HoTFT source on
the interpreted concatenation. -/
noncomputable def homotopy2_whiskerRight_refl_source_bridge_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (whiskerRight (Homotopy2.refl p) s))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))) :=
  HoTFT3.ofEq (homotopy2_in_HoTFT2_whiskerRight_refl p s)

/-- Interpreting the reflexive syntactic 2-cell on a concatenated path is
definitionally the reflexive HoTFT 2-cell on the interpreted concatenation. -/
theorem homotopy2_in_HoTFT2_refl_concat
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (Homotopy2.refl (ReductionSeq.concat p s)) =
      HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s)) :=
  rfl

/-- Triangle coherence for interpreted explicit paths at the HoTFT layer. -/
noncomputable def reductionSeq_triangle_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.trans
        (reductionSeq_associator_in_HoTFT2 p (ReductionSeq.refl M) q)
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p)
          (reductionSeq_leftUnitor_in_HoTFT2 q)))
      (HoTFT2.whiskerRight
        (reductionSeq_rightUnitor_in_HoTFT2 p)
        (reductionSeq_in_HoTFT1 q)) :=
  HoTFT3.triangle
    (reductionSeq_in_HoTFT1 p)
    (reductionSeq_in_HoTFT1 q)

/-- HoTFT 3-cell packaging the definitional bridge from the interpreted
syntactic reflexive target of `whiskerRightRefl` to the structural HoTFT
reflexive target on the concatenated path. -/
noncomputable def homotopy2_refl_concat_target_bridge_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (Homotopy2.refl (ReductionSeq.concat p s)))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))) :=
  HoTFT3.ofEq (homotopy2_in_HoTFT2_refl_concat p s)

/-- Left whiskering of an interpreted explicit 2-cell carries an explicit
HoTFT tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerLeft_in_HoTFTTetrahedron
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 α))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 q))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 p)) :=
  HoTFT3.whiskerLeftTetrahedron (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)

/-- Left whiskering commutes with vertical composition for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_whiskerLeftTrans_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s) :
    HoTFT3
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.trans (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)))
      (HoTFT2.trans
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α))
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 β))) :=
  HoTFT3.whiskerLeftTrans (reductionSeq_in_HoTFT1 r)
    (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)

/-- Left whiskering along a composite explicit path agrees with iterated left
whiskering plus the associator comparison on interpreted explicit HoTFT
2-cells. -/
noncomputable def homotopy2_whiskerLeftComp_in_HoTFT3
    {L M N P : Term} (p : ReductionSeq L M) (q : ReductionSeq M N)
    {r s : ReductionSeq N P} (α : Homotopy2 r s) :
    HoTFT3
      (HoTFT2.whiskerLeft
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
        (homotopy2_in_HoTFT2 α))
      (HoTFT2.trans
        (HoTFT2.associator
          (reductionSeq_in_HoTFT1 p)
          (reductionSeq_in_HoTFT1 q)
          (reductionSeq_in_HoTFT1 r))
        (HoTFT2.trans
          (HoTFT2.whiskerLeft
            (reductionSeq_in_HoTFT1 p)
            (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 q)
              (homotopy2_in_HoTFT2 α)))
          (HoTFT2.symm
            (HoTFT2.associator
              (reductionSeq_in_HoTFT1 p)
              (reductionSeq_in_HoTFT1 q)
              (reductionSeq_in_HoTFT1 s))))) :=
  HoTFT3.whiskerLeftComp
    (reductionSeq_in_HoTFT1 p)
    (reductionSeq_in_HoTFT1 q)
    (homotopy2_in_HoTFT2 α)

/-- HoTFT counterpart of `comparisonShellCompose_in_Theory3`. -/
noncomputable def comparisonShellCompose_in_HoTFT3
    {M N : Term}
    {αs αs' αm αm' αt αt' : HoTFT1 M N}
    (cₛ : HoTFT2 αs αs') (η : HoTFT2 αs αm)
    (cₘ : HoTFT2 αm αm') (θ : HoTFT2 αm αt)
    (cₜ : HoTFT2 αt αt') :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.trans (HoTFT2.symm cₛ) (HoTFT2.trans η cₘ))
        (HoTFT2.trans (HoTFT2.symm cₘ) (HoTFT2.trans θ cₜ)))
      (HoTFT2.trans (HoTFT2.symm cₛ)
        (HoTFT2.trans (HoTFT2.trans η θ) cₜ)) :=
  fun K => comparisonShellCompose_in_Theory3 K (cₛ K) (η K) (cₘ K) (θ K) (cₜ K)

/-- HoTFT counterpart of `homotopy2_whiskerLeft_bridge_in_Theory3`. -/
noncomputable def homotopy2_whiskerLeft_bridge_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (homotopy2_in_HoTFT2 (HigherTerms.whiskerLeft r α))
      (HoTFT2.trans
        (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 r p))
        (HoTFT2.trans
          (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α))
          (reductionSeq_comp_in_HoTFT2 r q))) :=
  fun K => homotopy2_whiskerLeft_bridge_in_Theory3 K r α

/-- Left whiskering commutes with symmetry for interpreted explicit HoTFT
2-cells. -/
noncomputable def homotopy2_whiskerLeftSymm_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.symm (homotopy2_in_HoTFT2 α)))
      (HoTFT2.symm
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
          (homotopy2_in_HoTFT2 α))) :=
  HoTFT3.whiskerLeftSymm (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)

/-- The inverse direction of left-whisker symmetry for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_invWhiskerLeft_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (HoTFT2.symm
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
          (homotopy2_in_HoTFT2 α)))
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))) :=
  HoTFT3.invWhiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)

/-- Right whiskering commutes with vertical composition for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_whiskerRightTrans_in_HoTFT3
    {L M N : Term} {p q s : ReductionSeq L M}
    (α : Homotopy2 p q) (β : Homotopy2 q s) (r : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.trans (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β))
        (reductionSeq_in_HoTFT1 r))
      (HoTFT2.trans
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α)
          (reductionSeq_in_HoTFT1 r))
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 β)
          (reductionSeq_in_HoTFT1 r))) :=
  HoTFT3.whiskerRightTrans
    (homotopy2_in_HoTFT2 α)
    (homotopy2_in_HoTFT2 β)
    (reductionSeq_in_HoTFT1 r)

/-- Right whiskering commutes with symmetry for interpreted explicit HoTFT
2-cells. -/
noncomputable def homotopy2_whiskerRightSymm_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))
        (reductionSeq_in_HoTFT1 s))
      (HoTFT2.symm
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α)
          (reductionSeq_in_HoTFT1 s))) :=
  HoTFT3.whiskerRightSymm (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)

/-- The inverse direction of right-whisker symmetry for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_invWhiskerRight_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.symm
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α)
          (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.whiskerRight
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))
        (reductionSeq_in_HoTFT1 s)) :=
  HoTFT3.invWhiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)

/-- Right composition with an interpreted explicit HoTFT 2-cell followed by its
inverse normalizes to the reflexive source 2-cell. -/
noncomputable def homotopy2_transRightCancel_in_HoTFT3
    {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (HoTFT2.trans
        (homotopy2_in_HoTFT2 α)
        (HoTFT2.symm (homotopy2_in_HoTFT2 α)))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 p)) :=
  HoTFT3.transRightCancel (homotopy2_in_HoTFT2 α)

/-- Left composition with the inverse of an interpreted explicit HoTFT 2-cell
normalizes to the reflexive target 2-cell. -/
noncomputable def homotopy2_transLeftCancel_in_HoTFT3
    {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))
        (homotopy2_in_HoTFT2 α))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 q)) :=
  HoTFT3.transLeftCancel (homotopy2_in_HoTFT2 α)

/-- Right whiskering of an interpreted explicit 2-cell carries an explicit
HoTFT tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerRight_in_HoTFTTetrahedron
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 s))
      (HoTFT1.whiskerRightTriangle (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)) :=
  HoTFT3.whiskerRightTetrahedron (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)

/-- Left whiskering preserves reflexive interpreted 2-cells up to a
proof-relevant HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerLeftRefl_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT2.refl
        (HoTFT1.comp (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 p))) :=
  HoTFTTetrahedron.path3
    (homotopy2_whiskerLeft_in_HoTFTTetrahedron r (Homotopy2.refl p))
    (reductionSeq_comp_refl_in_HoTFTTetrahedron r p)

/-- Structural left whiskering of a reflexive HoTFT 2-cell along an explicit
βη path normalizes directly to the reflexive interpreted composite HoTFT
1-cell. -/
noncomputable def reductionSeq_whiskerLeftRefl_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 r
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat r p))) :=
  fun K => reductionSeq_whiskerLeftRefl_in_Theory3 K r p

/-- A first boundary-aware 4-simplex comparison for right whiskering of a
reflexive interpreted 2-cell at the HoTFT layer. The remaining gap is now only
the final normalization of this tetrahedron into `HoTFT3`. -/
noncomputable def homotopy2_whiskerRightRefl_in_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s))) :=
  HoTFTTetrahedron.comparison
    (homotopy2_whiskerRight_in_HoTFTTetrahedron (Homotopy2.refl p) s)
    (reductionSeq_comp_refl_in_HoTFTTetrahedron p s)
    (homotopy2_whiskerRight_in_HoTFTTetrahedron (Homotopy2.refl p) s)

/-- The normalized HoTFT bridge tetrahedron for `whiskerRightRefl`. Its
fourth face is already the reflexive 2-cell on the semantic composite, so it
packages directly into a HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerRightRefl_bridge_in_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s)))) :=
  fun K => homotopy2_whiskerRightRefl_bridge_in_TheoryTetrahedron K p s

/-- Right whiskering preserves reflexive interpreted 2-cells up to a
proof-relevant HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerRightRefl_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
        (reductionSeq_in_HoTFT1 s))
      (HoTFT2.refl
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))) :=
  fun K => homotopy2_whiskerRightRefl_in_Theory3 K p s

/-- Naming wrapper for the normalized HoTFT `whiskerRightRefl` simplification
step for the standalone semantic right-whisker normalization witness. -/
noncomputable def reductionSeq_whiskerRight_refl_simplify_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
        (reductionSeq_in_HoTFT1 s))
      (HoTFT2.refl
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))) :=
  homotopy2_whiskerRightRefl_in_HoTFT3 p s

/-- HoTFT counterpart of `reductionSeq_whiskerRight_refl_inner_in_Theory3`. It
collapses the inner `trans w c` shell to `c`, isolating the final cancellation
step for the legacy unnormalized structural shell. -/
noncomputable def reductionSeq_whiskerRight_refl_inner_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s))
        (reductionSeq_comp_in_HoTFT2 p s))
      (reductionSeq_comp_in_HoTFT2 p s) :=
  HoTFT3.trans
    (HoTFT3.transCongrLeft
      (reductionSeq_whiskerRight_refl_simplify_in_HoTFT3 p s)
      (reductionSeq_comp_in_HoTFT2 p s))
    (HoTFT3.transReflLeft (reductionSeq_comp_in_HoTFT2 p s))

/-- HoTFT counterpart of `reductionSeq_whiskerRight_refl_bridge_in_Theory3`. -/
noncomputable def reductionSeq_whiskerRight_refl_bridge_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerRight_in_HoTFT2
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p)) s)
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))) :=
  fun K => reductionSeq_whiskerRight_refl_bridge_in_Theory3 K p s

/-- Interpreting a syntactic right whisker agrees with the legacy structural
right-whisker HoTFT shell, up to a HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerRight_bridge_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (whiskerRight α s))
      (reductionSeq_whiskerRight_in_HoTFT2 (homotopy2_in_HoTFT2 α) s) :=
  fun K => homotopy2_whiskerRight_bridge_in_Theory3 K α s

/-- HoTFT counterpart of `reductionSeq_whiskerRightOfEq_toOfEq_in_Theory3`. -/
noncomputable def reductionSeq_whiskerRightOfEq_toOfEq_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (h : p = q) (s : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerRight_in_HoTFT2
        (HoTFT2.ofEq (congrArg (fun r => reductionSeq_in_HoTFT1 r) h)) s)
      (HoTFT2.ofEq
        (congrArg (fun r => reductionSeq_in_HoTFT1 r)
          (congrArg (fun r => ReductionSeq.concat r s) h))) :=
  by
    cases h
    simpa [HoTFT2.ofEq] using reductionSeq_whiskerRight_refl_bridge_in_HoTFT3 p s

/-- HoTFT counterpart of `homotopy2_whiskerRightOfEq_toOfEq_in_Theory3`. -/
noncomputable def homotopy2_whiskerRightOfEq_toOfEq_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (h : p = q) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2
        (HigherTerms.whiskerRight (HigherTerms.Homotopy2.ofEq h) s))
      (HoTFT2.ofEq
        (congrArg (fun r => reductionSeq_in_HoTFT1 r)
          (congrArg (fun r => ReductionSeq.concat r s) h))) :=
  by
    exact HoTFT3.trans
      (HoTFT3.ofEq (homotopy2_in_HoTFT2_whiskerRight_ofEq h s))
      (reductionSeq_whiskerRightOfEq_toOfEq_in_HoTFT3 h s)

/-- HoTFT counterpart of `homotopy2_triangle_target_ofEq_toOfEq_in_Theory3`. -/
noncomputable def homotopy2_triangle_target_ofEq_toOfEq_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2
        (HigherTerms.whiskerRight (HigherTerms.rightUnitor p) q))
      (HoTFT2.ofEq
        (congrArg (fun r => reductionSeq_in_HoTFT1 r)
          (congrArg (fun r => ReductionSeq.concat r q)
            (ReductionSeq.concat_refl_right p)))) := by
  simpa [HigherTerms.rightUnitor] using
    (homotopy2_whiskerRightOfEq_toOfEq_in_HoTFT3
      (ReductionSeq.concat_refl_right p) q)

/-- HoTFT counterpart of
`homotopy2_pentagon_rightWhiskeredAssociator_target_ofEq_toOfEq_in_Theory3`. -/
noncomputable def homotopy2_pentagon_rightWhiskeredAssociator_target_ofEq_toOfEq_in_HoTFT3
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    HoTFT3
      (homotopy2_in_HoTFT2
        (HigherTerms.whiskerRight (HigherTerms.associator p q r) s))
      (HoTFT2.ofEq
        (congrArg (fun u => reductionSeq_in_HoTFT1 u)
          (congrArg (fun u => ReductionSeq.concat u s)
            (ReductionSeq.concat_assoc p q r)))) := by
  simpa [HigherTerms.associator] using
    (homotopy2_whiskerRightOfEq_toOfEq_in_HoTFT3
      (ReductionSeq.concat_assoc p q r) s)

/-- HoTFT counterpart of `reductionSeq_whiskerRightTrans_head_in_Theory3`. It
performs the same head normalization of the structural right-whisker
transitivity shell, leaving the remaining comparison-shell insertion problem
explicit. -/
noncomputable def reductionSeq_whiskerRightTrans_head_in_HoTFT3
    {L M N : Term} {p q r : ReductionSeq L M}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (θ : HoTFT2 (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))
    (s : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerRight_in_HoTFT2 (HoTFT2.trans η θ) s)
      (HoTFT2.trans
        (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 p s))
        (HoTFT2.trans
          (HoTFT2.trans
            (HoTFT2.whiskerRight η (reductionSeq_in_HoTFT1 s))
            (HoTFT2.whiskerRight θ (reductionSeq_in_HoTFT1 s)))
          (reductionSeq_comp_in_HoTFT2 r s))) :=
  fun K => reductionSeq_whiskerRightTrans_head_in_Theory3 K (η K) (θ K) s

/-- HoTFT counterpart of `reductionSeq_whiskerRightTrans_in_Theory3`. -/
noncomputable def reductionSeq_whiskerRightTrans_in_HoTFT3
    {L M N : Term} {p q r : ReductionSeq L M}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (θ : HoTFT2 (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))
    (s : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerRight_in_HoTFT2 (HoTFT2.trans η θ) s)
      (HoTFT2.trans
       (reductionSeq_whiskerRight_in_HoTFT2 η s)
       (reductionSeq_whiskerRight_in_HoTFT2 θ s)) :=
  fun K => reductionSeq_whiskerRightTrans_in_Theory3 K (η K) (θ K) s

/-- HoTFT counterpart of `reductionSeq_whiskerRightSymm_in_Theory3`. -/
noncomputable def reductionSeq_whiskerRightSymm_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (s : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerRight_in_HoTFT2 (HoTFT2.symm η) s)
      (HoTFT2.symm (reductionSeq_whiskerRight_in_HoTFT2 η s)) :=
  fun K => reductionSeq_whiskerRightSymm_in_Theory3 K (η K) s

/-- HoTFT counterpart of `homotopy2_whiskerRightTrans_bridge_in_Theory3`. -/
noncomputable def homotopy2_whiskerRightTrans_bridge_in_HoTFT3
    {L M N : Term} {p q r : ReductionSeq L M}
    (α : Homotopy2 p q) (β : Homotopy2 q r) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (whiskerRight (Homotopy2.trans α β) s))
      (HoTFT2.trans
        (homotopy2_in_HoTFT2 (whiskerRight α s))
        (homotopy2_in_HoTFT2 (whiskerRight β s))) :=
  fun K => homotopy2_whiskerRightTrans_bridge_in_Theory3 K α β s

/-- Every explicit syntactic 2-cell admits a reflexive semantic HoTFT 3-cell
over its interpreted HoTFT 2-cell. -/
noncomputable def homotopy2_refl_in_HoTFT3 {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    HoTFT3 (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 α) :=
  HoTFT3.refl (homotopy2_in_HoTFT2 α)

/-- Equality of explicit syntactic 2-cells induces a semantic HoTFT 3-cell
between their interpreted HoTFT 2-cells. -/
noncomputable def homotopy2_eq_in_HoTFT3 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (h : α = β) :
    HoTFT3 (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β) :=
  HoTFT3.ofEq (congrArg (fun γ => homotopy2_in_HoTFT2 γ) h)

/-- HoTFT counterpart of `homotopy2_rightUnitor_bridge_in_Theory3`. -/
noncomputable def homotopy2_rightUnitor_bridge_in_HoTFT3
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (HigherTerms.rightUnitor p))
      (reductionSeq_rightUnitor_shell_in_HoTFT2 p) := by
  intro K
  simpa [homotopy2_in_HoTFT2, reductionSeq_rightUnitor_shell_in_HoTFT2]
    using homotopy2_rightUnitor_bridge_in_Theory3 K p

/-- HoTFT counterpart of `homotopy2_leftUnitor_bridge_in_Theory3`. -/
noncomputable def homotopy2_leftUnitor_bridge_in_HoTFT3
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (HigherTerms.leftUnitor p))
      (reductionSeq_leftUnitor_shell_in_HoTFT2 p) :=
  fun K => homotopy2_leftUnitor_bridge_in_Theory3 K p

/-- HoTFT counterpart of
`homotopy2_whiskerLeft_leftUnitor_bridge_in_Theory3`. -/
noncomputable def homotopy2_whiskerLeft_leftUnitor_bridge_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (HigherTerms.whiskerLeft r (HigherTerms.leftUnitor p)))
      (reductionSeq_whiskerLeft_in_HoTFT2 r
        (reductionSeq_leftUnitor_shell_in_HoTFT2 p)) :=
  fun K => homotopy2_whiskerLeft_leftUnitor_bridge_in_Theory3 K r p

/-- HoTFT counterpart of `homotopy2_triangle_source_shell_in_Theory3`. -/
noncomputable def homotopy2_triangle_source_shell_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2
        (Homotopy2.trans (HigherTerms.associator p (ReductionSeq.refl M) q)
          (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q))))
      (HoTFT2.trans
        (HoTFT2.ofEq
          (congrArg (fun r => reductionSeq_in_HoTFT1 r)
            (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
        (reductionSeq_whiskerLeft_in_HoTFT2 p
          (reductionSeq_leftUnitor_shell_in_HoTFT2 q))) := by
  have hAssoc :
      HoTFT3
        (homotopy2_in_HoTFT2
          (HigherTerms.associator p (ReductionSeq.refl M) q))
        (HoTFT2.ofEq
          (congrArg (fun r => reductionSeq_in_HoTFT1 r)
            (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q))) := by
    simpa [HigherTerms.associator] using
      (HoTFT3.ofEq
        (homotopy2_in_HoTFT2_ofEq
          (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
  exact HoTFT3.trans
    (HoTFT3.transCongrLeft hAssoc
      (reductionSeq_whiskerLeft_in_HoTFT2 p
        (homotopy2_in_HoTFT2 (HigherTerms.leftUnitor q))))
    (HoTFT3.transCongrRight
      (HoTFT2.ofEq
        (congrArg (fun r => reductionSeq_in_HoTFT1 r)
          (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
      (homotopy2_whiskerLeft_leftUnitor_bridge_in_HoTFT3 p q))

/-- The semantic image of syntactic interchange is already a HoTFT 3-cell in
the current modelwise simplicial layer. -/
noncomputable def homotopy2_interchange_in_HoTFT3 {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HoTFT3
      (HoTFT2.hcomp (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β))
      (HoTFT2.trans
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 q))
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p') (homotopy2_in_HoTFT2 β))) :=
  HoTFT3.interchange (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)

/-- Alternative interchange on interpreted explicit 2-cells at the HoTFT
3-cell layer. -/
noncomputable def homotopy2_interchange'_in_HoTFT3 {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HoTFT3
      (HoTFT2.hcomp (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β))
      (HoTFT2.trans
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p) (homotopy2_in_HoTFT2 β))
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 q'))) :=
  HoTFT3.interchange' (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)

/-- HoTFT wrapper for the structural-endpoint `interchange'` bridge. -/
noncomputable def homotopy2_interchange'_bridge_in_HoTFT3 {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HoTFT3
      (homotopy2_in_HoTFT2 (HigherTerms.hcomp α β))
      (homotopy2_in_HoTFT2
        (Homotopy2.trans (HigherTerms.whiskerLeft p β)
          (HigherTerms.whiskerRight α q'))) :=
  fun K => homotopy2_interchange'_bridge_in_Theory3 K α β

/-- HoTFT counterpart of `homotopy2_triangle_in_Theory3`. -/
noncomputable def homotopy2_triangle_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2
        (Homotopy2.trans (HigherTerms.associator p (ReductionSeq.refl M) q)
          (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q))))
      (homotopy2_in_HoTFT2
        (HigherTerms.whiskerRight (HigherTerms.rightUnitor p) q)) :=
  fun K => homotopy2_triangle_in_Theory3 K p q

/-- HoTFT counterpart of `homotopy2_triangle_shell_in_Theory3`. -/
noncomputable def homotopy2_triangle_shell_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.ofEq
          (congrArg (fun r => reductionSeq_in_HoTFT1 r)
            (ReductionSeq.concat_assoc p (ReductionSeq.refl M) q)))
        (reductionSeq_whiskerLeft_in_HoTFT2 p
          (reductionSeq_leftUnitor_shell_in_HoTFT2 q)))
      (HoTFT2.ofEq
        (congrArg (fun r => reductionSeq_in_HoTFT1 r)
          (congrArg (fun r => ReductionSeq.concat r q)
            (ReductionSeq.concat_refl_right p)))) := by
  exact HoTFT3.trans
    (HoTFT3.symm (homotopy2_triangle_source_shell_in_HoTFT3 p q))
    (HoTFT3.trans
      (homotopy2_triangle_in_HoTFT3 p q)
      (homotopy2_triangle_target_ofEq_toOfEq_in_HoTFT3 p q))

/-- HoTFT counterpart of `homotopy2_pentagon_in_Theory3`. -/
noncomputable def homotopy2_pentagon_in_HoTFT3
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    HoTFT3
      (homotopy2_in_HoTFT2
        (Homotopy2.trans
          (HigherTerms.associator (ReductionSeq.concat p q) r s)
          (HigherTerms.associator p q (ReductionSeq.concat r s))))
      (homotopy2_in_HoTFT2
        (Homotopy2.trans
          (Homotopy2.trans
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s)
            (HigherTerms.associator p (ReductionSeq.concat q r) s))
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s)))) :=
  fun K => homotopy2_pentagon_in_Theory3 K p q r s

/-- Every structurally supported syntactic 3-cell between parallel explicit
2-cells induces a proof-relevant HoTFT 3-conversion between the corresponding
interpreted HoTFT 2-cells. -/
noncomputable def structuralHomotopy3_in_HoTFT3 :
    {M N : Term} → {p q : ReductionSeq M N} → {α β : Homotopy2 p q} →
      HigherLambdaModel.Lambda.HigherTerms.StructuralHomotopy3 α β →
        HoTFT3 (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)
  | _, _, _, _, _, _, .refl α =>
      homotopy2_refl_in_HoTFT3 α
  | _, _, _, _, _, _, .ofEq h =>
      homotopy2_eq_in_HoTFT3 h
  | _, _, _, _, _, _, .symm η =>
      HoTFT3.symm (structuralHomotopy3_in_HoTFT3 η)
  | _, _, _, _, _, _, .trans η θ =>
      HoTFT3.trans
        (structuralHomotopy3_in_HoTFT3 η)
        (structuralHomotopy3_in_HoTFT3 θ)
  | _, _, _, _, _, _, .transCongrLeft η θ =>
      HoTFT3.transCongrLeft
        (structuralHomotopy3_in_HoTFT3 η)
        (homotopy2_in_HoTFT2 θ)
  | _, _, _, _, _, _, .transCongrRight η θ =>
      HoTFT3.transCongrRight
        (homotopy2_in_HoTFT2 η)
        (structuralHomotopy3_in_HoTFT3 θ)
  | _, _, _, _, _, _, .whiskerLeftCongr r η =>
      reductionSeq_whiskerLeftCongr_in_HoTFT3 r
        (structuralHomotopy3_in_HoTFT3 η)
  | _, _, _, _, _, _, .whiskerLeftRefl r p =>
      reductionSeq_whiskerLeftRefl_in_HoTFT3 r p
  | _, _, _, _, _, _, .whiskerLeftTrans r α β =>
      reductionSeq_whiskerLeftTrans_in_HoTFT3 r
        (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)
  | _, _, _, _, _, _, .whiskerLeftSymm r α =>
      reductionSeq_whiskerLeftSymm_in_HoTFT3 r (homotopy2_in_HoTFT2 α)
  | _, _, _, _, _, _, .invWhiskerLeft r α =>
      HoTFT3.symm
        (reductionSeq_whiskerLeftSymm_in_HoTFT3 r (homotopy2_in_HoTFT2 α))
  | _, _, _, _, _, _, .whiskerRightRefl p s =>
      homotopy2_refl_in_HoTFT3 (Homotopy2.refl (ReductionSeq.concat p s))
  | _, _, _, _, _, _, .whiskerRightTrans α β s =>
      homotopy2_whiskerRightTrans_bridge_in_HoTFT3 α β s
  | _, _, _, _, _, _, .whiskerRightSymm α s =>
      HoTFT3.trans
        (homotopy2_whiskerRight_bridge_in_HoTFT3 (Homotopy2.symm α) s)
        (HoTFT3.trans
          (reductionSeq_whiskerRightSymm_in_HoTFT3
            (homotopy2_in_HoTFT2 α) s)
          (HoTFT3.symmCongr
            (HoTFT3.symm
              (homotopy2_whiskerRight_bridge_in_HoTFT3 α s))))
  | _, _, _, _, _, _, .invWhiskerRight α s =>
      HoTFT3.trans
        (HoTFT3.symmCongr
          (homotopy2_whiskerRight_bridge_in_HoTFT3 α s))
        (HoTFT3.trans
          (HoTFT3.symm
              (reductionSeq_whiskerRightSymm_in_HoTFT3
                (homotopy2_in_HoTFT2 α) s))
          (HoTFT3.symm
            (homotopy2_whiskerRight_bridge_in_HoTFT3 (Homotopy2.symm α) s)))
  | _, _, _, _, _, _, .interchange α β =>
      homotopy2_eq_in_HoTFT3 rfl
  | _, _, _, _, _, _, .interchange' α β =>
      homotopy2_interchange'_bridge_in_HoTFT3 α β
  | _, _, _, _, _, _, .pentagon p q r s =>
      homotopy2_pentagon_in_HoTFT3 p q r s
  | _, _, _, _, _, _, .triangle p q =>
      homotopy2_triangle_in_HoTFT3 p q

theorem beta_in_HoTFT (M N : Term) : (Term.app (Term.lam M) N) =_HoTFT (M[N]) := fun K ρ =>
  beta_sound K M N ρ

/-- The β-law also yields a proof-relevant semantic 1-conversion in every model. -/
noncomputable def beta_in_HoTFT1 (M N : Term) : HoTFT1 (Term.app (Term.lam M) N) (M[N]) :=
  betaEtaStep_in_HoTFT1 _ _ (BetaEtaStep.beta (BetaStep.beta M N))

theorem eta_in_HoTFT (M : Term) (h : Term.hasFreeVar 0 M = false) :
    (Term.lam (Term.app (Term.shift 1 0 M) (Term.var 0))) =_HoTFT M := fun K ρ =>
  eta_sound K M ρ h

/-- The η-law also yields a proof-relevant semantic 1-conversion in every model. -/
noncomputable def eta_in_HoTFT1 (M : Term) (h : Term.hasFreeVar 0 M = false) :
    HoTFT1 (Term.lam (Term.app (Term.shift 1 0 M) (Term.var 0))) M :=
  HoTFT1.ofHoTFTEq (eta_in_HoTFT M h)

/-- Every extensional Kan complex packages into the repository's lightweight
`HomotopicLambdaModel` interface. -/
noncomputable def ExtensionalKanComplex.toHomotopicLambdaModel
    (K : ExtensionalKanComplex) : HomotopicLambdaModel where
  carrier := K.Obj
  app := K.app
  lam := K.G
  beta := by
    intro f x
    exact K.eta f x
  ext := by
    intro M N hMN
    have hF : K.F M = K.F N := by
      funext x
      exact hMN x
    calc
      M = K.G (K.F M) := K.epsilon M
      _ = K.G (K.F N) := by rw [hF]
      _ = N := (K.epsilon N).symm
  PathSpace := K.PathSpace
  Path2 := fun {M N} p q => K.Path2 p q
  path2_refl := by
    intro M N p
    exact K.reflPath2 p

/-- The raw horn for the pentagon right-hand-side route: a 2-horn missing face 1
whose remaining faces are the degenerate front triangle on `q · (r · s)`,
the composition triangle, and the pentagon right-back triangle. -/
private def KanComplex.pentagonRHSRawHorn (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.reflPath2 (K.compPath q (K.compPath r s))).simplex
      else if h2 : i = 2 then (K.compTriangle p (K.compPath q (K.compPath r s))).simplex
      else (K.pentagonRightBackTriangle p q r s).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle p (K.compPath q (K.compPath r s))).face0.trans
          (K.reflPath2 (K.compPath q (K.compPath r s))).face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.pentagonRightBackTriangle p q r s).face0.trans
          (K.reflPath2 (K.compPath q (K.compPath r s))).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.pentagonRightBackTriangle p q r s).face2.trans
          (K.compTriangle p (K.compPath q (K.compPath r s))).face2.symm }

private def KanComplex.pentagonRHSRawSimplex (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) : K.Simplex 3 :=
  K.fill (K.pentagonRHSRawHorn p q r s)

/-- The raw Path2 extracted from the pentagon RHS horn fill. -/
private def KanComplex.pentagonRHSRawPath2 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path2
      (K.compPath (K.compPath (K.compPath p q) r) s)
      (K.compPath p (K.compPath q (K.compPath r s))) := by
  let Λ := K.pentagonRHSRawHorn p q r s
  refine
    { simplex := K.face 2 1 (K.pentagonRHSRawSimplex p q r s)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.pentagonRHSRawSimplex p q r s) =
        (K.reflPath2 (K.compPath q (K.compPath r s))).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.pentagonRHSRawSimplex p q r s))
          = K.face 1 0 (K.face 2 0 (K.pentagonRHSRawSimplex p q r s)) := by
              simpa using
                (K.face_face 1 (K.pentagonRHSRawSimplex p q r s)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.reflPath2 (K.compPath q (K.compPath r s))).simplex := by rw [h0]
      _ = (K.reflPath e).simplex := (K.reflPath2 (K.compPath q (K.compPath r s))).face0
  · have h2 : K.face 2 2 (K.pentagonRHSRawSimplex p q r s) =
        (K.compTriangle p (K.compPath q (K.compPath r s))).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.pentagonRHSRawSimplex p q r s))
          = K.face 1 1 (K.face 2 2 (K.pentagonRHSRawSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonRHSRawSimplex p q r s)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle p (K.compPath q (K.compPath r s))).simplex := by rw [h2]
      _ = (K.compPath p (K.compPath q (K.compPath r s))).simplex :=
            (K.compTriangle p (K.compPath q (K.compPath r s))).face1
  · have h3 : K.face 2 3 (K.pentagonRHSRawSimplex p q r s) =
        (K.pentagonRightBackTriangle p q r s).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.pentagonRHSRawSimplex p q r s))
          = K.face 1 1 (K.face 2 3 (K.pentagonRHSRawSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonRHSRawSimplex p q r s)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.pentagonRightBackTriangle p q r s).simplex := by rw [h3]
      _ = (K.compPath (K.compPath (K.compPath p q) r) s).simplex :=
            (K.pentagonRightBackTriangle p q r s).face1

/-- The boundary-aware tetrahedron from the pentagon RHS horn fill. -/
private def KanComplex.pentagonRHSRawTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.pentagonRHSRawPath2 p q r s).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonRightBackTriangle p q r s) := by
  let Λ := K.pentagonRHSRawHorn p q r s
  refine
    { simplex := K.pentagonRHSRawSimplex p q r s
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.pentagonRHSRawSimplex, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.pentagonRHSRawSimplex, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.pentagonRHSRawSimplex, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- The pure-Path2 pentagon comparison tetrahedron, obtained by comparing the
raw RHS route against the left-route associator. -/
private def KanComplex.pentagonComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.associatorPath2 p q (K.compPath r s)).toTriangle
      (K.pentagonRHSRawPath2 p q r s).toTriangle
      (K.associatorPath2 (K.compPath p q) r s).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.associatorTetrahedron p q (K.compPath r s))
    (K.pentagonBackComparisonTetrahedron p q r s)

/-- The raw pentagon Path3 from the left route to the horn-fill-determined
right route. -/
private def KanComplex.pentagonRawPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.pentagonRHSRawPath2 p q r s) :=
  K.tetrahedronFace2Path3
    (K.reflPath3 (K.associatorPath2 (K.compPath p q) r s))
    (K.transFillerTetrahedron
      (K.associatorPath2 (K.compPath p q) r s)
      (K.associatorPath2 p q (K.compPath r s)))
    (K.pentagonComparisonTetrahedron p q r s)

/-- Contracting the loop comparing the two pentagon back triangles is enough to
normalize the back-face comparison to a reflexive middle face. -/
private def KanComplex.pentagonBackComparisonFromLoopContraction (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (Κ :
      K.Path3
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s))
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).toTriangle
      (K.pentagonRightBackTriangle p q r s)
      (K.pentagonInnerBackTriangle p q r s) :=
  K.tetrahedronReplaceFace1 Κ
    (K.pentagonInnerBackComparisonTetrahedron p q r s)

private def KanComplex.pentagonInnerRightReflHorn (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    Horn K.toSimplicialSet 2 0 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h1 : i = 1 then
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).simplex
      else if h2 : i = 2 then
        (K.pentagonRightBackTriangle p q r s).simplex
      else
        (K.pentagonInnerBackTriangle p q r s).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h12 | h13 | h23
      · rcases h12 with ⟨rfl, rfl⟩
        simpa using
          (K.pentagonRightBackTriangle p q r s).face1.trans
            (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).face1.symm
      · rcases h13 with ⟨rfl, rfl⟩
        simpa using
          (K.pentagonInnerBackTriangle p q r s).face1.trans
            (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using
          (K.pentagonInnerBackTriangle p q r s).face2.trans
            (K.pentagonRightBackTriangle p q r s).face2.symm }

/-- The raw Horn[2,0]-filler behind the remaining pentagon back comparison. -/
private def KanComplex.pentagonInnerRightReflSimplex (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) : K.Simplex 3 :=
  K.fill (K.pentagonInnerRightReflHorn p q r s)

/-- The unresolved front face of the Horn[2,0]-filler whose other faces are
the reflexive back edge, the canonical right-back triangle, and the inner-back
triangle. Proving that this front face contracts to `reflPath2` is the
remaining semantic pentagon blocker. -/
def KanComplex.pentagonInnerRightFrontPath2 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path2
      (K.compPath q (K.compPath r s))
      (K.compPath q (K.compPath r s)) := by
  let Λ := K.pentagonInnerRightReflHorn p q r s
  refine
    { simplex := K.face 2 0 (K.pentagonInnerRightReflSimplex p q r s)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h1 :
        K.face 2 1 (K.pentagonInnerRightReflSimplex p q r s) =
          (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 0 (K.pentagonInnerRightReflSimplex p q r s))
          = K.face 1 0 (K.face 2 1 (K.pentagonInnerRightReflSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonInnerRightReflSimplex p q r s)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).simplex := by
            rw [h1]
      _ = (K.reflPath e).simplex := (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).face0
  · have h2 :
        K.face 2 2 (K.pentagonInnerRightReflSimplex p q r s) =
          (K.pentagonRightBackTriangle p q r s).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 0 (K.pentagonInnerRightReflSimplex p q r s))
          = K.face 1 0 (K.face 2 2 (K.pentagonInnerRightReflSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonInnerRightReflSimplex p q r s)
                  (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 0 (K.pentagonRightBackTriangle p q r s).simplex := by
            rw [h2]
      _ = (K.compPath q (K.compPath r s)).simplex :=
            (K.pentagonRightBackTriangle p q r s).face0
  · have h3 :
        K.face 2 3 (K.pentagonInnerRightReflSimplex p q r s) =
          (K.pentagonInnerBackTriangle p q r s).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 0 (K.pentagonInnerRightReflSimplex p q r s))
          = K.face 1 0 (K.face 2 3 (K.pentagonInnerRightReflSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonInnerRightReflSimplex p q r s)
                  (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 1 0 (K.pentagonInnerBackTriangle p q r s).simplex := by
            rw [h3]
      _ = (K.compPath q (K.compPath r s)).simplex :=
            (K.pentagonInnerBackTriangle p q r s).face0

/-- The Horn[2,0]-filler already provides the desired back, right, and inner
faces for the missing pentagon tetrahedron; only its front face still needs to
be contracted to the reflexive 2-cell on `q · (r · s)`. -/
def KanComplex.pentagonInnerRightReflCandidateTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.pentagonInnerRightFrontPath2 p q r s).toTriangle
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).toTriangle
      (K.pentagonRightBackTriangle p q r s)
      (K.pentagonInnerBackTriangle p q r s) := by
  let Λ := K.pentagonInnerRightReflHorn p q r s
  refine
    { simplex := K.pentagonInnerRightReflSimplex p q r s
      face0 := rfl
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.pentagonInnerRightReflSimplex, Λ] using
      (K.fill_spec Λ (i := 1) (by omega) (by omega))
  · simpa [KanComplex.pentagonInnerRightReflSimplex, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.pentagonInnerRightReflSimplex, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- A contraction of the unresolved front face suffices to remove the remaining
pentagon axiom. -/
def KanComplex.pentagonBackComparisonReflPath3OfFrontPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (frontContract :
      K.Path3
        (K.pentagonInnerRightFrontPath2 p q r s)
        (K.reflPath2 (K.compPath q (K.compPath r s)))) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  K.symmPath3 <|
    K.tetrahedronFrontPath3 frontContract
      (K.pentagonInnerRightReflCandidateTetrahedron p q r s)
      (K.pentagonInnerBackComparisonTetrahedron p q r s)

/-- Conversely, a contraction of the back-triangle comparison loop determines
the remaining reduced front-face contraction. -/
private def KanComplex.pentagonInnerRightFrontReflPath3OfBackPath3
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (backContract :
      K.Path3
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s))
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s))) :=
  K.tetrahedronFace0Path3
    (K.pentagonInnerRightReflCandidateTetrahedron p q r s)
    (K.pentagonBackComparisonFromLoopContraction p q r s backContract)

/-!
### Pentagon back-triangle coherence: the bare Kan frontier

The helper chain below isolates the smallest remaining obstruction in a bare
`KanComplex`: the reduced front-face contraction

  `K.Path3 (K.pentagonInnerRightFrontPath2 p q r s)
     (K.reflPath2 outerRight)`

where `outerRight = compPath q (compPath r s)` is the common outer-right edge of
the canonical Horn[2,0]-filler whose remaining faces are the reflexive back
edge, the canonical right-back triangle, and the inner-back triangle.

The new helper chain

* `pentagonInnerRightReflHorn`
* `pentagonInnerRightReflSimplex`
* `pentagonInnerRightFrontPath2`
* `pentagonInnerRightReflCandidateTetrahedron`
* `pentagonBackComparisonReflPath3OfFrontPath3`

extracts the canonical Horn[2,0]-filler all the way to a boundary-aware
tetrahedron.  So the remaining blocker is now reduced to the smallest possible
front-face contraction:

  `K.Path3 (K.pentagonInnerRightFrontPath2 p q r s)
     (K.reflPath2 (K.compPath q (K.compPath r s)))`

Once that front contraction is available, the older back-comparison theorem
`pentagonBackComparisonReflPath3` follows immediately from
`pentagonBackComparisonReflPath3OfFrontPath3`.

Conversely, `pentagonInnerRightFrontReflPath3OfBackPath3` now shows that any
contraction of the back-triangle loop also yields the front contraction, so the
remaining gap is exactly the absence of either seed contraction in a bare
`KanComplex`.

At the semantic model layer this stronger coherence can be packaged separately
in `CoherentExtensionalKanComplex.pentagonPath3`, while the base
`ExtensionalKanComplex` interface still suffices for the explicit syntactic
pentagon theorem and `StrictKanComplex`/`StrictExtensionalKanComplex` derive the
coherent extension axiom-free from filler uniqueness.
-/

/-- The target 3-fold composite on the right side of the pentagon identity,
connected to the horn-fill raw path by `tetrahedronPath3`. Both tetrahedra
share the same boundary except face 1, so `tetrahedronPath3` extracts the
bridge Path3 between the two face 1 cells.

Current state:

* The normalized-front comparison layer is already implemented via
  `pentagonFrontComparisonTetrahedron`,
  `pentagonWhiskerFrontComparisonPath3`,
  `pentagonStep1BoundaryCoreTetrahedron`, and
  `pentagonStep12BoundaryCoreTetrahedron`.
* The full triple-composite right-hand route also has a boundary-aware
  tetrahedron `pentagonStep123BoundaryCoreTetrahedron`.
* So the remaining gap is now strictly smaller than before: the full boundary
  tetrahedron is no longer postulated directly. It is reconstructed from a
  smaller back-only 3-cell `pentagonBackComparisonReflPath3`, which contracts
  the comparison between `pentagonInnerBackTriangle p q r s` and
  `pentagonRightBackTriangle p q r s` to reflexivity on the common back edge.
-/
private noncomputable def KanComplex.pentagonBoundaryTetrahedronFromMiddleComparison (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (middleComparison :
      K.Tetrahedron
        (K.reflPath2 (K.reflPath e)).toTriangle
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s)).toTriangle) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonRightBackTriangle p q r s) := by
  let ε := K.reflTriangleTetrahedron
    ((K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle)
  let ω := K.pentagonStep123BoundaryCoreTetrahedron p q r s
  let κ := K.pentagonInnerBackComparisonTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then middleComparison.simplex
        else if h3 : i = 3 then ω.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using middleComparison.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω.face1.trans middleComparison.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans middleComparison.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω.face3.symm
      }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = middleComparison.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 middleComparison.simplex := by rw [h1]
      _ = (K.transPath2
            (K.transPath2
              (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
              (K.associatorPath2 p (K.compPath q r) s))
            (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle.simplex :=
          middleComparison.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h3]
      _ = (K.compTriangle p (K.compPath q (K.compPath r s))).simplex := ω.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.pentagonRightBackTriangle p q r s).simplex := κ.face2

/-- Comparing the raw RHS horn-fill tetrahedron against the normalized
step-1/2/3 boundary core keeps the back comparison explicit while isolating the
middle-face difference between the raw horn-fill route and the fully normalized
right-hand composite. -/
private noncomputable def KanComplex.pentagonRawBigComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.pentagonRHSRawPath2 p q r s).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.pentagonStep123BoundaryCoreTetrahedron p q r s)
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.pentagonInnerBackComparisonTetrahedron p q r s)

/-- Comparing the normalized step-1/2/3 boundary core against the canonical
left-hand pentagon boundary keeps the same back-triangle comparison explicit
while isolating the middle-face difference between the normalized right-hand
composite and the left-hand composite route. -/
noncomputable def KanComplex.pentagonLeftBigComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.pentagonStep123BoundaryCoreTetrahedron p q r s)
    (K.pentagonRightBoundaryCoreTetrahedron p q r s)
    (K.pentagonInnerBackComparisonTetrahedron p q r s)

/-- Even before the back comparison contracts, the two big comparison
tetrahedra already give a direct semantic 3-cell from the raw RHS horn-fill
route back to the left-associated pentagon route. This packages the remaining
gap as the comparison between two different left-to-raw proofs. -/
private noncomputable def KanComplex.pentagonRawLeftComparisonPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonRHSRawPath2 p q r s)
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))) :=
  K.tetrahedronPath3
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.pentagonRightBoundaryCoreTetrahedron p q r s)

/-- The left-associated pentagon route also reaches the raw RHS horn-fill route
through the same back-comparison face that remains unresolved later on. -/
private noncomputable def KanComplex.pentagonRawAlternativePath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.pentagonRHSRawPath2 p q r s) :=
  K.symmPath3 (K.pentagonRawLeftComparisonPath3 p q r s)

/-- If the back-triangle comparison contracts to reflexivity, then the raw RHS
comparison tetrahedron upgrades to the smaller back-normalization tetrahedron
used by `pentagonBoundaryTetrahedronFromMiddleComparison`. -/
private noncomputable def KanComplex.pentagonBackNormalizationTetrahedronFromBackContract
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (backContract :
      K.Path3
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s))
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.tetrahedronReplaceFace1
    (K.symmPath3
      (K.tetrahedronFace2Path3 backContract
        (K.pentagonRawBigComparisonTetrahedron p q r s)
        ((K.reflPath3 (K.pentagonRHSRawPath2 p q r s)).toTetrahedron)))
    (K.pentagonRawBigComparisonTetrahedron p q r s)

/-- A direct pentagon 3-cell on the canonical associator composites already forces
the reduced back-triangle comparison loop to contract. This shows the isolated
bare-Kan pentagon blocker is weaker than the full semantic pentagon coherence on
the same four composable 1-cells. -/
private noncomputable def KanComplex.pentagonBackComparisonReflPath3OfMiddlePath3
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (middlePath :
      K.Path3
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s)))
        (K.pentagonRHSRawPath2 p q r s)) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  K.tetrahedronFace3Path3 middlePath
    (K.pentagonRawBigComparisonTetrahedron p q r s)
    ((K.reflPath3 (K.pentagonRHSRawPath2 p q r s)).toTetrahedron)

/-- Any direct semantic pentagon 3-cell on four composable 1-cells contracts the
reduced back-triangle comparison loop isolated above. -/
noncomputable def KanComplex.pentagonBackComparisonReflPath3OfPentagonPath3
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (pentagonPath :
      K.Path3
        (K.transPath2
          (K.associatorPath2 (K.compPath p q) r s)
          (K.associatorPath2 p q (K.compPath r s)))
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s)))) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) := by
  exact K.pentagonBackComparisonReflPath3OfMiddlePath3 p q r s
    (K.transPath3
      (K.symmPath3 pentagonPath)
      (K.pentagonRawAlternativePath3 p q r s))

/-- Consequently, any direct semantic pentagon 3-cell also determines the reduced
front-face contraction at the bare-Kan pentagon frontier. -/
noncomputable def KanComplex.pentagonInnerRightFrontReflPath3OfPentagonPath3
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (pentagonPath :
      K.Path3
        (K.transPath2
          (K.associatorPath2 (K.compPath p q) r s)
          (K.associatorPath2 p q (K.compPath r s)))
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s)))) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s))) := by
  exact K.pentagonInnerRightFrontReflPath3OfBackPath3 p q r s
    (K.pentagonBackComparisonReflPath3OfPentagonPath3 p q r s pentagonPath)

/-- Conversely, contracting the reduced back-triangle comparison loop is already
enough to reconstruct the full direct semantic pentagon 3-cell. -/
noncomputable def KanComplex.pentagonPath3OfBackComparisonReflPath3
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (backContract :
      K.Path3
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s))
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) := by
  let middleComparison :=
    K.pentagonBackNormalizationTetrahedronFromBackContract p q r s backContract
  let boundary :=
    K.pentagonBoundaryTetrahedronFromMiddleComparison p q r s middleComparison
  exact K.symmPath3 <|
    K.tetrahedronPath3 boundary (K.pentagonRightBoundaryCoreTetrahedron p q r s)

/-- So the reduced front-face contraction at the bare-Kan pentagon frontier is
also enough to recover the full direct semantic pentagon 3-cell. -/
noncomputable def KanComplex.pentagonPath3OfInnerRightFrontReflPath3
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (frontContract :
      K.Path3
        (K.pentagonInnerRightFrontPath2 p q r s)
        (K.reflPath2 (K.compPath q (K.compPath r s)))) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) := by
  exact K.pentagonPath3OfBackComparisonReflPath3 p q r s
    (K.pentagonBackComparisonReflPath3OfFrontPath3 p q r s frontContract)

/-- Pointwise lift of `KanComplex.pentagonBackComparisonReflPath3OfPentagonPath3`.

Any direct semantic pentagon 3-cell already contracts the reduced back-triangle
comparison loop. -/
noncomputable def Theory3.pentagonBackComparisonReflOfPentagonPath3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q)
    (pentagonPath :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K (Theory1.comp K α β) γ δ)
          (Theory2.associator K α β (Theory1.comp K γ δ)))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
            (Theory2.associator K α (Theory1.comp K β γ) δ))
          (Theory2.whiskerLeft K α (Theory2.associator K β γ δ)))) :
    Theory3 K
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
            (α ρ) (β ρ) (γ ρ) (δ ρ))
          (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
            (α ρ) (β ρ) (γ ρ) (δ ρ)))
      (Theory2.refl K
        (Theory1.comp K
          (Theory1.comp K (Theory1.comp K α β) γ) δ)) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.pentagonBackComparisonReflPath3OfPentagonPath3
      (α ρ) (β ρ) (γ ρ) (δ ρ) (pentagonPath ρ)

/-- Pointwise lift of `KanComplex.pentagonInnerRightFrontReflPath3OfPentagonPath3`.

So a direct semantic pentagon 3-cell also determines the reduced front-face
contraction at the bare-Kan pentagon frontier. -/
noncomputable def Theory3.pentagonInnerRightFrontReflOfPentagonPath3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q)
    (pentagonPath :
      Theory3 K
        (Theory2.trans K
          (Theory2.associator K (Theory1.comp K α β) γ δ)
          (Theory2.associator K α β (Theory1.comp K γ δ)))
        (Theory2.trans K
          (Theory2.trans K
            (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
            (Theory2.associator K α (Theory1.comp K β γ) δ))
          (Theory2.whiskerLeft K α (Theory2.associator K β γ δ)))) :
    Theory3 K
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
          (α ρ) (β ρ) (γ ρ) (δ ρ))
      (Theory2.refl K
        (Theory1.comp K β (Theory1.comp K γ δ))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontReflPath3OfPentagonPath3
      (α ρ) (β ρ) (γ ρ) (δ ρ) (pentagonPath ρ)

/-- Pointwise lift of `KanComplex.pentagonPath3OfBackComparisonReflPath3`.

So the reduced back-triangle comparison loop is actually equivalent to the full
direct semantic pentagon coherence. -/
noncomputable def Theory3.pentagonOfBackComparisonRefl
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q)
    (backPath :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
              (α ρ) (β ρ) (γ ρ) (δ ρ))
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
              (α ρ) (β ρ) (γ ρ) (δ ρ)))
        (Theory2.refl K
          (Theory1.comp K
            (Theory1.comp K (Theory1.comp K α β) γ) δ))) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.comp K α β) γ δ)
        (Theory2.associator K α β (Theory1.comp K γ δ)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
          (Theory2.associator K α (Theory1.comp K β γ) δ))
        (Theory2.whiskerLeft K α (Theory2.associator K β γ δ))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.pentagonPath3OfBackComparisonReflPath3
      (α ρ) (β ρ) (γ ρ) (δ ρ) (backPath ρ)

/-- Pointwise lift of `KanComplex.pentagonPath3OfInnerRightFrontReflPath3`.

So the reduced front-face contraction is also equivalent to the full direct
semantic pentagon coherence. -/
noncomputable def Theory3.pentagonOfInnerRightFrontRefl
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q)
    (frontPath :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
            (α ρ) (β ρ) (γ ρ) (δ ρ))
        (Theory2.refl K
          (Theory1.comp K β (Theory1.comp K γ δ)))) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.comp K α β) γ δ)
        (Theory2.associator K α β (Theory1.comp K γ δ)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
          (Theory2.associator K α (Theory1.comp K β γ) δ))
        (Theory2.whiskerLeft K α (Theory2.associator K β γ δ))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.pentagonPath3OfInnerRightFrontReflPath3
      (α ρ) (β ρ) (γ ρ) (δ ρ) (frontPath ρ)

/-- Pointwise lift of `KanComplex.pentagonInnerRightFrontReflPath3OfBackPath3`.

So any contraction of the reduced back-triangle comparison loop already yields
the reduced front-face contraction. -/
noncomputable def Theory3.pentagonInnerRightFrontReflOfBackPath3
    (K : ExtensionalKanComplex) {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q)
    (backPath :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
              (α ρ) (β ρ) (γ ρ) (δ ρ))
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
              (α ρ) (β ρ) (γ ρ) (δ ρ)))
        (Theory2.refl K
          (Theory1.comp K
            (Theory1.comp K (Theory1.comp K α β) γ) δ))) :
    Theory3 K
      (fun ρ =>
        K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
          (α ρ) (β ρ) (γ ρ) (δ ρ))
      (Theory2.refl K
        (Theory1.comp K β (Theory1.comp K γ δ))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontReflPath3OfBackPath3
      (α ρ) (β ρ) (γ ρ) (δ ρ) (backPath ρ)

/-- HoTFT counterpart of `Theory3.pentagonBackComparisonReflOfPentagonPath3`. -/
noncomputable def HoTFT3.pentagonBackComparisonReflOfPentagonPath3
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q)
    (pentagonPath :
      HoTFT3
        (HoTFT2.trans
          (HoTFT2.associator (HoTFT1.comp α β) γ δ)
          (HoTFT2.associator α β (HoTFT1.comp γ δ)))
        (HoTFT2.trans
          (HoTFT2.trans
            (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
            (HoTFT2.associator α (HoTFT1.comp β γ) δ))
          (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ)))) :
    HoTFT3
      (fun K ρ =>
        K.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
            (α K ρ) (β K ρ) (γ K ρ) (δ K ρ))
          (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
            (α K ρ) (β K ρ) (γ K ρ) (δ K ρ)))
      (HoTFT2.refl
        (HoTFT1.comp
          (HoTFT1.comp (HoTFT1.comp α β) γ) δ)) :=
  fun K =>
    Theory3.pentagonBackComparisonReflOfPentagonPath3
      K (α K) (β K) (γ K) (δ K) (pentagonPath K)

/-- HoTFT counterpart of `Theory3.pentagonOfBackComparisonRefl`. -/
noncomputable def HoTFT3.pentagonOfBackComparisonRefl
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q)
    (backPath :
      HoTFT3
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
              (α K ρ) (β K ρ) (γ K ρ) (δ K ρ))
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
              (α K ρ) (β K ρ) (γ K ρ) (δ K ρ)))
        (HoTFT2.refl
          (HoTFT1.comp
            (HoTFT1.comp (HoTFT1.comp α β) γ) δ))) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.comp α β) γ δ)
        (HoTFT2.associator α β (HoTFT1.comp γ δ)))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
          (HoTFT2.associator α (HoTFT1.comp β γ) δ))
        (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ))) :=
  fun K =>
    Theory3.pentagonOfBackComparisonRefl
      K (α K) (β K) (γ K) (δ K) (backPath K)

/-- HoTFT counterpart of `Theory3.pentagonInnerRightFrontReflOfBackPath3`. -/
noncomputable def HoTFT3.pentagonInnerRightFrontReflOfBackPath3
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q)
    (backPath :
      HoTFT3
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
              (α K ρ) (β K ρ) (γ K ρ) (δ K ρ))
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
              (α K ρ) (β K ρ) (γ K ρ) (δ K ρ)))
        (HoTFT2.refl
          (HoTFT1.comp
            (HoTFT1.comp (HoTFT1.comp α β) γ) δ))) :
    HoTFT3
      (fun K ρ =>
        K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
          (α K ρ) (β K ρ) (γ K ρ) (δ K ρ))
      (HoTFT2.refl
        (HoTFT1.comp β (HoTFT1.comp γ δ))) :=
  fun K =>
    Theory3.pentagonInnerRightFrontReflOfBackPath3
      K (α K) (β K) (γ K) (δ K) (backPath K)

/-- HoTFT counterpart of `Theory3.pentagonOfInnerRightFrontRefl`. -/
noncomputable def HoTFT3.pentagonOfInnerRightFrontRefl
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q)
    (frontPath :
      HoTFT3
        (fun K ρ =>
          K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
            (α K ρ) (β K ρ) (γ K ρ) (δ K ρ))
        (HoTFT2.refl
          (HoTFT1.comp β (HoTFT1.comp γ δ)))) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.comp α β) γ δ)
        (HoTFT2.associator α β (HoTFT1.comp γ δ)))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
          (HoTFT2.associator α (HoTFT1.comp β γ) δ))
        (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ))) :=
  fun K =>
    Theory3.pentagonOfInnerRightFrontRefl
      K (α K) (β K) (γ K) (δ K) (frontPath K)

/-- HoTFT counterpart of `Theory3.pentagonInnerRightFrontReflOfPentagonPath3`. -/
noncomputable def HoTFT3.pentagonInnerRightFrontReflOfPentagonPath3
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q)
    (pentagonPath :
      HoTFT3
        (HoTFT2.trans
          (HoTFT2.associator (HoTFT1.comp α β) γ δ)
          (HoTFT2.associator α β (HoTFT1.comp γ δ)))
        (HoTFT2.trans
          (HoTFT2.trans
            (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
            (HoTFT2.associator α (HoTFT1.comp β γ) δ))
          (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ)))) :
    HoTFT3
      (fun K ρ =>
        K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
          (α K ρ) (β K ρ) (γ K ρ) (δ K ρ))
      (HoTFT2.refl
        (HoTFT1.comp β (HoTFT1.comp γ δ))) :=
  HoTFT3.pentagonInnerRightFrontReflOfBackPath3 α β γ δ
    (HoTFT3.pentagonBackComparisonReflOfPentagonPath3 α β γ δ pentagonPath)

/-- A bare extensional Kan model becomes coherent as soon as one supplies the
reduced back-triangle pentagon contraction together with WLWR coherence. -/
noncomputable def ExtensionalKanComplex.toCoherentExtensionalKanComplexOfPentagonBackComparisonRefl
    (K : ExtensionalKanComplex)
    (pentagonBackComparisonRefl :
      ∀ {a b c d e : K.toReflexiveKanComplex.Obj}
        (p : K.toReflexiveKanComplex.PathSpace a b)
        (q : K.toReflexiveKanComplex.PathSpace b c)
        (r : K.toReflexiveKanComplex.PathSpace c d)
        (s : K.toReflexiveKanComplex.PathSpace d e),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle p q r s)
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle p q r s))
          (K.toReflexiveKanComplex.reflPath2
            (K.toReflexiveKanComplex.compPath
              (K.toReflexiveKanComplex.compPath
                (K.toReflexiveKanComplex.compPath p q) r) s)))
    (wlwrPath3 :
      ∀ {a b c d : K.toReflexiveKanComplex.Obj}
        (α : K.toReflexiveKanComplex.PathSpace a b)
        {β γ : K.toReflexiveKanComplex.PathSpace b c}
        (η : K.toReflexiveKanComplex.Path2 β γ)
        (δ : K.toReflexiveKanComplex.PathSpace c d),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.whiskerRightPath2
            (K.toReflexiveKanComplex.whiskerLeftPath2 α η) δ)
          (K.toReflexiveKanComplex.transPath2
            (K.toReflexiveKanComplex.associatorPath2 α β δ)
            (K.toReflexiveKanComplex.transPath2
              (K.toReflexiveKanComplex.whiskerLeftPath2 α
                (K.toReflexiveKanComplex.whiskerRightPath2 η δ))
              (K.toReflexiveKanComplex.symmPath2
                (K.toReflexiveKanComplex.associatorPath2 α γ δ))))) :
    CoherentExtensionalKanComplex where
  toExtensionalKanComplex := K
  pentagonPath3 := fun p q r s =>
    K.toReflexiveKanComplex.toKanComplex.pentagonPath3OfBackComparisonReflPath3 p q r s
      (pentagonBackComparisonRefl p q r s)
  wlwrPath3 := wlwrPath3

/-- Equivalently, the smaller front-face pentagon seed together with WLWR
coherence already determines a coherent extensional Kan model. -/
noncomputable def ExtensionalKanComplex.toCoherentExtensionalKanComplexOfPentagonInnerRightFrontRefl
    (K : ExtensionalKanComplex)
    (pentagonInnerRightFrontRefl :
      ∀ {a b c d e : K.toReflexiveKanComplex.Obj}
        (p : K.toReflexiveKanComplex.PathSpace a b)
        (q : K.toReflexiveKanComplex.PathSpace b c)
        (r : K.toReflexiveKanComplex.PathSpace c d)
        (s : K.toReflexiveKanComplex.PathSpace d e),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2 p q r s)
          (K.toReflexiveKanComplex.reflPath2
            (K.toReflexiveKanComplex.compPath q
              (K.toReflexiveKanComplex.compPath r s))))
    (wlwrPath3 :
      ∀ {a b c d : K.toReflexiveKanComplex.Obj}
        (α : K.toReflexiveKanComplex.PathSpace a b)
        {β γ : K.toReflexiveKanComplex.PathSpace b c}
        (η : K.toReflexiveKanComplex.Path2 β γ)
        (δ : K.toReflexiveKanComplex.PathSpace c d),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.whiskerRightPath2
            (K.toReflexiveKanComplex.whiskerLeftPath2 α η) δ)
          (K.toReflexiveKanComplex.transPath2
            (K.toReflexiveKanComplex.associatorPath2 α β δ)
            (K.toReflexiveKanComplex.transPath2
              (K.toReflexiveKanComplex.whiskerLeftPath2 α
                (K.toReflexiveKanComplex.whiskerRightPath2 η δ))
              (K.toReflexiveKanComplex.symmPath2
                (K.toReflexiveKanComplex.associatorPath2 α γ δ))))) :
    CoherentExtensionalKanComplex where
  toExtensionalKanComplex := K
  pentagonPath3 := fun p q r s =>
    K.toReflexiveKanComplex.toKanComplex.pentagonPath3OfInnerRightFrontReflPath3 p q r s
      (pentagonInnerRightFrontRefl p q r s)
  wlwrPath3 := wlwrPath3

/-- A reduced coherent extensional Kan model packages the smallest pentagon datum
currently known to suffice for the recursive associator theorem: the inner-right
front contraction together with WLWR coherence. -/
structure FrontSeedCoherentExtensionalKanComplex extends ExtensionalKanComplex where
  pentagonInnerRightFrontReflPath3 :
    ∀ {a b c d e : toExtensionalKanComplex.toReflexiveKanComplex.Obj}
      (p : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace a b)
      (q : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace b c)
      (r : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace c d)
      (s : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace d e),
      toExtensionalKanComplex.toReflexiveKanComplex.Path3
        (KanComplex.pentagonInnerRightFrontPath2
          toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex p q r s)
        (toExtensionalKanComplex.toReflexiveKanComplex.reflPath2
          (toExtensionalKanComplex.toReflexiveKanComplex.compPath q
            (toExtensionalKanComplex.toReflexiveKanComplex.compPath r s)))
  wlwrPath3 :
    ∀ {a b c d : toExtensionalKanComplex.toReflexiveKanComplex.Obj}
      (α : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace a b)
      {β γ : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace b c}
      (η : toExtensionalKanComplex.toReflexiveKanComplex.Path2 β γ)
      (δ : toExtensionalKanComplex.toReflexiveKanComplex.PathSpace c d),
      toExtensionalKanComplex.toReflexiveKanComplex.Path3
        (toExtensionalKanComplex.toReflexiveKanComplex.whiskerRightPath2
          (toExtensionalKanComplex.toReflexiveKanComplex.whiskerLeftPath2 α η) δ)
        (toExtensionalKanComplex.toReflexiveKanComplex.transPath2
          (toExtensionalKanComplex.toReflexiveKanComplex.associatorPath2 α β δ)
          (toExtensionalKanComplex.toReflexiveKanComplex.transPath2
            (toExtensionalKanComplex.toReflexiveKanComplex.whiskerLeftPath2 α
              (toExtensionalKanComplex.toReflexiveKanComplex.whiskerRightPath2 η δ))
            (toExtensionalKanComplex.toReflexiveKanComplex.symmPath2
              (toExtensionalKanComplex.toReflexiveKanComplex.associatorPath2 α γ δ))))

/-- The reduced front-seed coherence package induces a full coherent extensional
Kan model. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.toCoherentExtensionalKanComplex
    (K : FrontSeedCoherentExtensionalKanComplex) :
    CoherentExtensionalKanComplex :=
  K.toExtensionalKanComplex.toCoherentExtensionalKanComplexOfPentagonInnerRightFrontRefl
    K.pentagonInnerRightFrontReflPath3 K.wlwrPath3

/-- Every coherent extensional Kan model induces the smaller front-seed coherence
package. -/
noncomputable def CoherentExtensionalKanComplex.toFrontSeedCoherentExtensionalKanComplex
    (K : CoherentExtensionalKanComplex) :
    FrontSeedCoherentExtensionalKanComplex where
  toExtensionalKanComplex := K.toExtensionalKanComplex
  pentagonInnerRightFrontReflPath3 := fun p q r s =>
    KanComplex.pentagonInnerRightFrontReflPath3OfPentagonPath3
      K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex p q r s
      (K.pentagonPath3 p q r s)
  wlwrPath3 := K.wlwrPath3

/-- Pentagon coherence at the semantic 3-cell layer for coherent extensional Kan
complexes. -/
noncomputable def Theory3.pentagon
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    (β : Theory1 K.toExtensionalKanComplex M N)
    (γ : Theory1 K.toExtensionalKanComplex N P)
    (δ : Theory1 K.toExtensionalKanComplex P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex α β) γ δ)
        (Theory2.associator K.toExtensionalKanComplex α β
          (Theory1.comp K.toExtensionalKanComplex γ δ)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex α β γ) δ)
          (Theory2.associator K.toExtensionalKanComplex α
            (Theory1.comp K.toExtensionalKanComplex β γ) δ))
         (Theory2.whiskerLeft K.toExtensionalKanComplex α
           (Theory2.associator K.toExtensionalKanComplex β γ δ))) :=
  fun ρ => K.pentagonPath3 (α ρ) (β ρ) (γ ρ) (δ ρ)

/-- Backward-compatible alias for coherent semantic pentagon coherence. -/
noncomputable def Theory3.pentagonPath3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    (β : Theory1 K.toExtensionalKanComplex M N)
    (γ : Theory1 K.toExtensionalKanComplex N P)
    (δ : Theory1 K.toExtensionalKanComplex P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex α β) γ δ)
        (Theory2.associator K.toExtensionalKanComplex α β
          (Theory1.comp K.toExtensionalKanComplex γ δ)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex α β γ) δ)
          (Theory2.associator K.toExtensionalKanComplex α
            (Theory1.comp K.toExtensionalKanComplex β γ) δ))
       (Theory2.whiskerLeft K.toExtensionalKanComplex α
          (Theory2.associator K.toExtensionalKanComplex β γ δ))) :=
  Theory3.pentagon K α β γ δ

/-- In a coherent model, the pentagon field contracts the reduced back-triangle
comparison loop automatically. -/
noncomputable def Theory3.coherentPentagonBackComparisonRefl
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    (β : Theory1 K.toExtensionalKanComplex M N)
    (γ : Theory1 K.toExtensionalKanComplex N P)
    (δ : Theory1 K.toExtensionalKanComplex P Q) :
    Theory3 K.toExtensionalKanComplex
      (fun ρ =>
        K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
            (α ρ) (β ρ) (γ ρ) (δ ρ))
          (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
            (α ρ) (β ρ) (γ ρ) (δ ρ)))
      (Theory2.refl K.toExtensionalKanComplex
        (Theory1.comp K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex
            (Theory1.comp K.toExtensionalKanComplex α β) γ) δ)) :=
  Theory3.pentagonBackComparisonReflOfPentagonPath3
    K.toExtensionalKanComplex α β γ δ (Theory3.pentagon K α β γ δ)

/-- In a coherent model, the pentagon field also contracts the reduced
front-face loop at the bare-Kan pentagon frontier. -/
noncomputable def Theory3.coherentPentagonInnerRightFrontRefl
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    (β : Theory1 K.toExtensionalKanComplex M N)
    (γ : Theory1 K.toExtensionalKanComplex N P)
    (δ : Theory1 K.toExtensionalKanComplex P Q) :
    Theory3 K.toExtensionalKanComplex
      (fun ρ =>
        K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
          (α ρ) (β ρ) (γ ρ) (δ ρ))
      (Theory2.refl K.toExtensionalKanComplex
        (Theory1.comp K.toExtensionalKanComplex β
          (Theory1.comp K.toExtensionalKanComplex γ δ))) :=
  Theory3.pentagonInnerRightFrontReflOfBackPath3
    K.toExtensionalKanComplex α β γ δ
    (Theory3.coherentPentagonBackComparisonRefl K α β γ δ)

/-- Pentagon coherence for interpreted explicit reduction sequences in a fixed
coherent extensional Kan complex. Unlike `homotopy2_pentagon_in_Theory3`, this
stronger wrapper speaks directly in terms of semantic associator cells and
therefore uses the extra coherent-model pentagon field. -/
noncomputable def reductionSeq_pentagon_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
        (Theory2.associator K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
          (Theory2.associator K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (Theory2.associator K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))) :=
  Theory3.pentagon K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

/-- Coherent pentagon coherence contracts the reduced back-triangle comparison for
interpreted explicit reduction sequences. -/
noncomputable def reductionSeq_pentagonBackComparisonRefl_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (fun ρ =>
        K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex p) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex q) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex r) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ))
          (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex p) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex q) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex r) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ)))
      (Theory2.refl K.toExtensionalKanComplex
        (Theory1.comp K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))) :=
  Theory3.coherentPentagonBackComparisonRefl K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

/-- Coherent pentagon coherence also contracts the reduced front-face loop for
interpreted explicit reduction sequences. -/
noncomputable def reductionSeq_pentagonInnerRightFrontRefl_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (fun ρ =>
        K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2
          ((reductionSeq_in_Theory1 K.toExtensionalKanComplex p) ρ)
          ((reductionSeq_in_Theory1 K.toExtensionalKanComplex q) ρ)
          ((reductionSeq_in_Theory1 K.toExtensionalKanComplex r) ρ)
          ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ))
      (Theory2.refl K.toExtensionalKanComplex
        (Theory1.comp K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))) :=
  Theory3.coherentPentagonInnerRightFrontRefl K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

/-- WLWR interchange coherence for coherent extensional Kan models.
Right-whiskering distributes over left-whiskering up to the bracketing
associators.  This is the `CoherentExtensionalKanComplex` counterpart of
`Theory3.strictWhiskerLeftWhiskerRight` (proved from filler uniqueness in the
strict setting); here we simply unpack the `wlwrPath3` model field. -/
noncomputable def Theory3.coherentWhiskerLeftWhiskerRight
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    {β γ : Theory1 K.toExtensionalKanComplex M N}
    (η : Theory2 K.toExtensionalKanComplex β γ)
    (δ : Theory1 K.toExtensionalKanComplex N P) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.whiskerRight K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex α η) δ)
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex α β δ)
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerLeft K.toExtensionalKanComplex α
            (Theory2.whiskerRight K.toExtensionalKanComplex η δ))
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex α γ δ)))) :=
  fun ρ => K.wlwrPath3 (α ρ) (η ρ) (δ ρ)

/-- Refl-specialized forward base theorem: a reduced WLWR right-half comparison
on a single leading forward step already yields the full associator shell
comparison for that one-step path. -/
noncomputable def reductionSeq_comp_associator_step_refl_in_Theory3_of_rightComparison
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hRight :
      let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ)))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s (ReductionSeq.refl M)) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K0 r
  have hMidFront :
      let γ := reductionSeq_in_Theory1 K0
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.pentagonWhiskerFrontPath2
            (α ρ) (γ ρ) (δ ρ)) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightPentagonWhiskerFrontComparisonFromTriangleComparison
        K0 α η δ hRight)
  have hTri :
      let β := Theory1.comp K0
        (reductionSeq_in_Theory1 K0 (ReductionSeq.refl M))
        (reductionSeq_in_Theory1 K0 q)
      let γ := reductionSeq_in_Theory1 K0
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.transPath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K0.toReflexiveKanComplex.toKanComplex.symmPath2
              (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ)))) := by
    simpa using
      (reductionSeq_comp_triangle_target_step_in_Theory3 K0 s
        (ReductionSeq.refl M) q r hMidFront)
  have hHead :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0
          (ReductionSeq.step s (ReductionSeq.refl M)) q r)
        (Theory2.whiskerLeft K0
          (betaEtaStep_in_Theory1 K0 L M s)
          (reductionSeq_associator_shell_in_Theory2 K0
            (ReductionSeq.refl M) q r)) :=
    reductionSeq_comp_associator_stepHead_from_triangle_in_Theory3 K s
      (ReductionSeq.refl M) q r hTri
  exact reductionSeq_comp_associator_step_finish_in_Theory3 K0 s
    (ReductionSeq.refl M) q r
    (reductionSeq_comp_associator_refl_in_Theory3 K0 q r)
    hHead

/-- Refl-specialized forward base theorem, wired from the normalized frontier
`mid ; symm assoc ~ right`. -/
noncomputable def reductionSeq_comp_associator_step_refl_in_Theory3_of_normalizedRightComparison
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNorm :
      let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ) (η ρ))
            (δ ρ))) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s (ReductionSeq.refl M)) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K0 r
  have hRight :
      let γ := reductionSeq_in_Theory1 K0
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      Theory3 K0
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ)).toTriangle
            (K0.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K0.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K0.toReflexiveKanComplex.toKanComplex.symmPath2
            (K0.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (γ ρ) (δ ρ))) := by
    simpa [α, η, δ] using
      (Theory3.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
        K0 α η δ hNorm)
  exact reductionSeq_comp_associator_step_refl_in_Theory3_of_rightComparison
    K s q r hRight

/-- Refl-specialized forward base theorem, wired from the smaller nested-whisker
comparison
`assoc ; whiskerLeft (whiskerRight leftUnitor δ) ; symm assoc ~ right`. -/
  noncomputable def reductionSeq_comp_associator_step_refl_in_Theory3_of_nestedWhiskerComparison
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P)
    (hNested :
      let α := betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s
      let β := Theory1.comp K.toExtensionalKanComplex
        (Theory1.refl K.toExtensionalKanComplex M)
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
      let η := reductionSeq_comp_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.refl M) q
      let γ := reductionSeq_in_Theory1 K.toExtensionalKanComplex
        (ReductionSeq.concat (ReductionSeq.refl M) q)
      let δ := reductionSeq_in_Theory1 K.toExtensionalKanComplex r
      Theory3 K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.associator K.toExtensionalKanComplex α β δ)
          (Theory2.trans K.toExtensionalKanComplex
            (Theory2.whiskerLeft K.toExtensionalKanComplex α
              (Theory2.whiskerRight K.toExtensionalKanComplex η δ))
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex α γ δ))))
        (Theory2.whiskerRight K.toExtensionalKanComplex
          (Theory2.whiskerLeft K.toExtensionalKanComplex α η) δ)) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s (ReductionSeq.refl M)) q r))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let β := Theory1.comp K0 (Theory1.refl K0 M) (reductionSeq_in_Theory1 K0 q)
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let γ := reductionSeq_in_Theory1 K0 (ReductionSeq.concat (ReductionSeq.refl M) q)
  let δ := reductionSeq_in_Theory1 K0 r
  have hNorm :
      Theory3 K0
        (Theory2.trans K0
          (fun ρ =>
            K0.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightMidPath2
              (α ρ) (η ρ) (δ ρ))
          (Theory2.symm K0 (Theory2.associator K0 α γ δ)))
        (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α η) δ) := by
    simpa [α, β, η, γ, δ] using
      (reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
        K0 α η δ hNested)
  exact reductionSeq_comp_associator_step_refl_in_Theory3_of_normalizedRightComparison
    K s q r hNorm


/-- Unconditional forward-step base theorem for the refl tail:
given a `CoherentExtensionalKanComplex`, the structural associator shell
for a one-step path `(step s (refl M))` against `q` and `r` compares against
the equality-induced 2-cell.  The WLWR interchange is supplied by the model
field `wlwrPath3`. -/
noncomputable def reductionSeq_comp_associator_step_refl_in_Theory3
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.step s (ReductionSeq.refl M)) q r))) :=
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K0 r
  reductionSeq_comp_associator_step_refl_in_Theory3_of_nestedWhiskerComparison K s q r
    (Theory3.symm K0 (Theory3.coherentWhiskerLeftWhiskerRight K α η δ))

/-- Unconditional inverse-step base theorem for the refl tail:
given a `CoherentExtensionalKanComplex`, the structural associator shell
for a one-step inverse path `(stepInv s (refl M))` against `q` and `r`
compares against the equality-induced 2-cell. -/
noncomputable def reductionSeq_comp_associator_stepInv_refl_in_Theory3
    (K : CoherentExtensionalKanComplex) {L M N P : Term}
    (s : BetaEtaStep M L) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc (ReductionSeq.stepInv s (ReductionSeq.refl M)) q r))) :=
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let η := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.refl M) q
  let δ := reductionSeq_in_Theory1 K0 r
  reductionSeq_comp_associator_stepInv_refl_in_Theory3_of_nestedWhiskerComparison K s q r
    (Theory3.symm K0 (Theory3.coherentWhiskerLeftWhiskerRight K α η δ))

/-- The recursive associator comparison already follows from the reduced
back-triangle pentagon seed plus WLWR coherence, via the induced coherent
extensional Kan model. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_ofPentagonBackComparisonRefl
    (K : ExtensionalKanComplex)
    (pentagonBackComparisonRefl :
      ∀ {a b c d e : K.toReflexiveKanComplex.Obj}
        (p : K.toReflexiveKanComplex.PathSpace a b)
        (q : K.toReflexiveKanComplex.PathSpace b c)
        (r : K.toReflexiveKanComplex.PathSpace c d)
        (s : K.toReflexiveKanComplex.PathSpace d e),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle p q r s)
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle p q r s))
          (K.toReflexiveKanComplex.reflPath2
            (K.toReflexiveKanComplex.compPath
              (K.toReflexiveKanComplex.compPath
                (K.toReflexiveKanComplex.compPath p q) r) s)))
    (wlwrPath3 :
      ∀ {a b c d : K.toReflexiveKanComplex.Obj}
        (α : K.toReflexiveKanComplex.PathSpace a b)
        {β γ : K.toReflexiveKanComplex.PathSpace b c}
        (η : K.toReflexiveKanComplex.Path2 β γ)
        (δ : K.toReflexiveKanComplex.PathSpace c d),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.whiskerRightPath2
            (K.toReflexiveKanComplex.whiskerLeftPath2 α η) δ)
          (K.toReflexiveKanComplex.transPath2
            (K.toReflexiveKanComplex.associatorPath2 α β δ)
            (K.toReflexiveKanComplex.transPath2
              (K.toReflexiveKanComplex.whiskerLeftPath2 α
                (K.toReflexiveKanComplex.whiskerRightPath2 η δ))
              (K.toReflexiveKanComplex.symmPath2
                (K.toReflexiveKanComplex.associatorPath2 α γ δ)))))
    {L M N P : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_associator_shell_in_Theory2 K p q r)
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (ReductionSeq.concat_assoc p q r))) := by
  let Kc :=
    K.toCoherentExtensionalKanComplexOfPentagonBackComparisonRefl
      pentagonBackComparisonRefl wlwrPath3
  let K0 := Kc.toExtensionalKanComplex
  simpa [Kc, ExtensionalKanComplex.toCoherentExtensionalKanComplexOfPentagonBackComparisonRefl] using
    (reductionSeq_comp_associator_in_Theory3_of_normalizedRightComparisons Kc
      (fun {_ _ _ _ _} s rest q r =>
        let α := betaEtaStep_in_Theory1 K0 _ _ s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
          K0 α η δ (Theory3.symm K0 (Theory3.coherentWhiskerLeftWhiskerRight Kc α η δ)))
      (fun {_ _ _ _ _} s rest q r =>
        let α := betaEtaStepInv_in_Theory1 K0 _ _ s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
          K0 α η δ (Theory3.symm K0 (Theory3.coherentWhiskerLeftWhiskerRight Kc α η δ)))
      p q r)

/-- Equivalently, the recursive associator comparison already follows from the
smaller front-face pentagon seed plus WLWR coherence. -/
noncomputable def reductionSeq_comp_associator_in_Theory3_ofPentagonInnerRightFrontRefl
    (K : ExtensionalKanComplex)
    (pentagonInnerRightFrontRefl :
      ∀ {a b c d e : K.toReflexiveKanComplex.Obj}
        (p : K.toReflexiveKanComplex.PathSpace a b)
        (q : K.toReflexiveKanComplex.PathSpace b c)
        (r : K.toReflexiveKanComplex.PathSpace c d)
        (s : K.toReflexiveKanComplex.PathSpace d e),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2 p q r s)
          (K.toReflexiveKanComplex.reflPath2
            (K.toReflexiveKanComplex.compPath q
              (K.toReflexiveKanComplex.compPath r s))))
    (wlwrPath3 :
      ∀ {a b c d : K.toReflexiveKanComplex.Obj}
        (α : K.toReflexiveKanComplex.PathSpace a b)
        {β γ : K.toReflexiveKanComplex.PathSpace b c}
        (η : K.toReflexiveKanComplex.Path2 β γ)
        (δ : K.toReflexiveKanComplex.PathSpace c d),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.whiskerRightPath2
            (K.toReflexiveKanComplex.whiskerLeftPath2 α η) δ)
          (K.toReflexiveKanComplex.transPath2
            (K.toReflexiveKanComplex.associatorPath2 α β δ)
            (K.toReflexiveKanComplex.transPath2
              (K.toReflexiveKanComplex.whiskerLeftPath2 α
                (K.toReflexiveKanComplex.whiskerRightPath2 η δ))
              (K.toReflexiveKanComplex.symmPath2
                (K.toReflexiveKanComplex.associatorPath2 α γ δ)))))
    {L M N P : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K
      (reductionSeq_associator_shell_in_Theory2 K p q r)
      (Theory2.ofEq K
        (congrArg (fun u => reductionSeq_in_Theory1 K u)
          (ReductionSeq.concat_assoc p q r))) := by
  let Kc :=
    K.toCoherentExtensionalKanComplexOfPentagonInnerRightFrontRefl
      pentagonInnerRightFrontRefl wlwrPath3
  let K0 := Kc.toExtensionalKanComplex
  simpa [Kc, ExtensionalKanComplex.toCoherentExtensionalKanComplexOfPentagonInnerRightFrontRefl] using
    (reductionSeq_comp_associator_in_Theory3_of_normalizedRightComparisons Kc
      (fun {_ _ _ _ _} s rest q r =>
        let α := betaEtaStep_in_Theory1 K0 _ _ s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
          K0 α η δ (Theory3.symm K0 (Theory3.coherentWhiskerLeftWhiskerRight Kc α η δ)))
      (fun {_ _ _ _ _} s rest q r =>
        let α := betaEtaStepInv_in_Theory1 K0 _ _ s
        let η := reductionSeq_comp_in_Theory2 K0 rest q
        let δ := reductionSeq_in_Theory1 K0 r
        reductionSeq_comp_associator_refl_normalizedRightComparison_of_nestedWhiskerComparison
          K0 α η δ (Theory3.symm K0 (Theory3.coherentWhiskerLeftWhiskerRight Kc α η δ)))
      p q r)

/-- The recursive associator comparison for the reduced front-seed coherence
boundary. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.reductionSeq_comp_associator_in_Theory3
    (K : FrontSeedCoherentExtensionalKanComplex)
    {L M N P : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc p q r))) :=
  reductionSeq_comp_associator_in_Theory3_ofPentagonInnerRightFrontRefl
    K.toExtensionalKanComplex K.pentagonInnerRightFrontReflPath3 K.wlwrPath3 p q r

/-- Main unconditional recursive associator comparison for coherent extensional
Kan models. Rather than routing through the older normalized-right recursive
proof directly, we pass through the reduced front-seed coherence package already
induced by every coherent model. -/
noncomputable def reductionSeq_comp_associator_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc p q r))) :=
  K.toFrontSeedCoherentExtensionalKanComplex.reductionSeq_comp_associator_in_Theory3 p q r

/-- In a coherent extensional Kan model, the interpreted equality-generated
associator 2-cell agrees with the structural associator shell. This is the
coherent counterpart of the strict bridge theorem and packages the new
recursive associator comparison as a direct statement about the explicit
associator syntax. -/
noncomputable def homotopy2_associator_coherent_bridge_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (HigherTerms.associator p q r))
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r) := by
  exact homotopy2_associator_bridge_in_Theory3_of_compAssociator
    K.toExtensionalKanComplex
    (reductionSeq_comp_associator_in_Theory3 K) p q r

/-- The explicit associator bridge already follows at the reduced front-seed
coherence boundary. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.homotopy2_associator_bridge_in_Theory3
    (K : FrontSeedCoherentExtensionalKanComplex)
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (HigherTerms.associator p q r))
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r) := by
  exact homotopy2_associator_bridge_in_Theory3_of_compAssociator
    K.toExtensionalKanComplex
    (FrontSeedCoherentExtensionalKanComplex.reductionSeq_comp_associator_in_Theory3 K) p q r

/-- The direct semantic pentagon on interpreted reduction sequences already
follows from the reduced back-triangle pentagon seed. -/
noncomputable def reductionSeq_pentagon_in_Theory3_ofPentagonBackComparisonRefl
    (K : ExtensionalKanComplex)
    (pentagonBackComparisonRefl :
      ∀ {a b c d e : K.toReflexiveKanComplex.Obj}
        (p : K.toReflexiveKanComplex.PathSpace a b)
        (q : K.toReflexiveKanComplex.PathSpace b c)
        (r : K.toReflexiveKanComplex.PathSpace c d)
        (s : K.toReflexiveKanComplex.PathSpace d e),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.pentagonInnerBackTriangle p q r s)
            (K.toReflexiveKanComplex.toKanComplex.pentagonRightBackTriangle p q r s))
          (K.toReflexiveKanComplex.reflPath2
            (K.toReflexiveKanComplex.compPath
              (K.toReflexiveKanComplex.compPath
                (K.toReflexiveKanComplex.compPath p q) r) s)))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K
          (Theory1.comp K
            (reductionSeq_in_Theory1 K p)
            (reductionSeq_in_Theory1 K q))
          (reductionSeq_in_Theory1 K r)
          (reductionSeq_in_Theory1 K s))
        (Theory2.associator K
          (reductionSeq_in_Theory1 K p)
          (reductionSeq_in_Theory1 K q)
          (Theory1.comp K
            (reductionSeq_in_Theory1 K r)
            (reductionSeq_in_Theory1 K s))))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K
            (Theory2.associator K
              (reductionSeq_in_Theory1 K p)
              (reductionSeq_in_Theory1 K q)
              (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s))
          (Theory2.associator K
            (reductionSeq_in_Theory1 K p)
            (Theory1.comp K
              (reductionSeq_in_Theory1 K q)
              (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s)))
        (Theory2.whiskerLeft K
          (reductionSeq_in_Theory1 K p)
          (Theory2.associator K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)
            (reductionSeq_in_Theory1 K s)))) := by
  exact Theory3.pentagonOfBackComparisonRefl K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)
    (reductionSeq_in_Theory1 K s)
    (fun ρ =>
      pentagonBackComparisonRefl
        ((reductionSeq_in_Theory1 K p) ρ)
        ((reductionSeq_in_Theory1 K q) ρ)
        ((reductionSeq_in_Theory1 K r) ρ)
        ((reductionSeq_in_Theory1 K s) ρ))

/-- Equivalently, the direct semantic pentagon on interpreted reduction
sequences already follows from the smaller front-face pentagon seed. -/
noncomputable def reductionSeq_pentagon_in_Theory3_ofPentagonInnerRightFrontRefl
    (K : ExtensionalKanComplex)
    (pentagonInnerRightFrontRefl :
      ∀ {a b c d e : K.toReflexiveKanComplex.Obj}
        (p : K.toReflexiveKanComplex.PathSpace a b)
        (q : K.toReflexiveKanComplex.PathSpace b c)
        (r : K.toReflexiveKanComplex.PathSpace c d)
        (s : K.toReflexiveKanComplex.PathSpace d e),
        K.toReflexiveKanComplex.Path3
          (K.toReflexiveKanComplex.toKanComplex.pentagonInnerRightFrontPath2 p q r s)
          (K.toReflexiveKanComplex.reflPath2
            (K.toReflexiveKanComplex.compPath q
              (K.toReflexiveKanComplex.compPath r s))))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K
          (Theory1.comp K
            (reductionSeq_in_Theory1 K p)
            (reductionSeq_in_Theory1 K q))
          (reductionSeq_in_Theory1 K r)
          (reductionSeq_in_Theory1 K s))
        (Theory2.associator K
          (reductionSeq_in_Theory1 K p)
          (reductionSeq_in_Theory1 K q)
          (Theory1.comp K
            (reductionSeq_in_Theory1 K r)
            (reductionSeq_in_Theory1 K s))))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K
            (Theory2.associator K
              (reductionSeq_in_Theory1 K p)
              (reductionSeq_in_Theory1 K q)
              (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s))
          (Theory2.associator K
            (reductionSeq_in_Theory1 K p)
            (Theory1.comp K
              (reductionSeq_in_Theory1 K q)
              (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s)))
        (Theory2.whiskerLeft K
          (reductionSeq_in_Theory1 K p)
          (Theory2.associator K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)
            (reductionSeq_in_Theory1 K s)))) := by
  exact Theory3.pentagonOfInnerRightFrontRefl K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)
    (reductionSeq_in_Theory1 K s)
    (fun ρ =>
      pentagonInnerRightFrontRefl
        ((reductionSeq_in_Theory1 K p) ρ)
        ((reductionSeq_in_Theory1 K q) ρ)
        ((reductionSeq_in_Theory1 K r) ρ)
        ((reductionSeq_in_Theory1 K s) ρ))

/-- The reduced front-seed coherence boundary already determines the full direct
semantic pentagon on interpreted reduction sequences. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.reductionSeq_pentagon_in_Theory3
    (K : FrontSeedCoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
        (Theory2.associator K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
          (Theory2.associator K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (Theory2.associator K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))) := by
  exact reductionSeq_pentagon_in_Theory3_ofPentagonInnerRightFrontRefl
    K.toExtensionalKanComplex K.pentagonInnerRightFrontReflPath3 p q r s

/-- In a coherent extensional Kan model, the source endpoint of the explicit
pentagon 3-cell bridges to the structural associator shells. -/
noncomputable def homotopy2_pentagon_source_coherent_bridge_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (HigherTerms.associator (ReductionSeq.concat p q) r s)
          (HigherTerms.associator p q (ReductionSeq.concat r s))))
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s))) := by
  exact homotopy2_pentagon_source_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_coherent_bridge_in_Theory3 K) p q r s

/-- In a coherent extensional Kan model, the target endpoint of the explicit
pentagon 3-cell bridges to the mixed shell where the right-whiskered factor is
still equality-generated. -/
noncomputable def homotopy2_pentagon_target_coherent_bridge_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (Homotopy2.trans
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s)
            (HigherTerms.associator p (ReductionSeq.concat q r) s))
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s))))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_target_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_coherent_bridge_in_Theory3 K) p q r s

/-- In a coherent extensional Kan model, the explicit pentagon identifies the
structural source shell with the mixed target shell. This isolates the live
pentagon mismatch to the right-whiskered factor. -/
noncomputable def homotopy2_pentagon_shell_coherent_bridge_in_Theory3
    (K : CoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_shell_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_coherent_bridge_in_Theory3 K) p q r s

/-- At the reduced front-seed boundary, the source endpoint of the explicit
pentagon already bridges to the structural associator shells. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.homotopy2_pentagon_source_bridge_in_Theory3
    (K : FrontSeedCoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (HigherTerms.associator (ReductionSeq.concat p q) r s)
          (HigherTerms.associator p q (ReductionSeq.concat r s))))
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s))) := by
  exact homotopy2_pentagon_source_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (FrontSeedCoherentExtensionalKanComplex.homotopy2_associator_bridge_in_Theory3 K)
    p q r s

/-- At the reduced front-seed boundary, the target endpoint of the explicit
pentagon bridges to the mixed shell where the right-whiskered factor is still
equality-generated. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.homotopy2_pentagon_target_bridge_in_Theory3
    (K : FrontSeedCoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (Homotopy2.trans
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s)
            (HigherTerms.associator p (ReductionSeq.concat q r) s))
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s))))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_target_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (FrontSeedCoherentExtensionalKanComplex.homotopy2_associator_bridge_in_Theory3 K)
    p q r s

/-- At the reduced front-seed boundary, the explicit pentagon already identifies
the structural source shell with the mixed target shell. -/
noncomputable def FrontSeedCoherentExtensionalKanComplex.homotopy2_pentagon_shell_bridge_in_Theory3
    (K : FrontSeedCoherentExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_shell_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (FrontSeedCoherentExtensionalKanComplex.homotopy2_associator_bridge_in_Theory3 K)
    p q r s


end HigherLambdaModel.Lambda.ExtensionalKan
