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

/-- The boundary-aware tetrahedron whose middle face is right whiskering at the
HoTFT semantic layer. -/
noncomputable def HoTFT3.whiskerRightTetrahedron {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :=
  fun K => Theory3.whiskerRightTetrahedron K (η K) (γ K)

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

/-- Interpreting a reflexive syntactic right whisker in a fixed model unfolds
definitionally to the reflexive semantic 2-cell on the interpreted
concatenation. -/
theorem homotopy2_in_Theory2_whiskerRight_refl
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_Theory2 K (whiskerRight (Homotopy2.refl p) s) =
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s)) :=
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
private def KanComplex.pentagonInnerRightFrontPath2 (K : KanComplex)
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
private def KanComplex.pentagonInnerRightReflCandidateTetrahedron (K : KanComplex)
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
private def KanComplex.pentagonBackComparisonReflPath3OfFrontPath3 (K : KanComplex)
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

/-!
### Pentagon back-triangle coherence: the remaining frontier

The last axiom in this file is `pentagonInnerRightFrontReflPath3`. It asserts
the smallest remaining semantic 3-cell

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

**What would close the gap.**
•  A `StrictKanComplex` (unique fillers) would make
   `pentagonInnerRightFrontPath2 p q r s` definitionally equal to
   `reflPath2 outerRight`.
•  Any general lemma contracting `Path2 u u` loops with the boundary carried by
   `pentagonInnerRightFrontPath2` to `reflPath2 u` would also suffice.
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
private noncomputable def KanComplex.pentagonLeftBigComparisonTetrahedron (K : KanComplex)
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

private axiom KanComplex.pentagonInnerRightFrontReflPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s)))

/-- The older back-triangle comparison theorem is now derived from the smaller
front-face contraction on the canonical Horn[2,0]-filler. -/
noncomputable def KanComplex.pentagonBackComparisonReflPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  K.pentagonBackComparisonReflPath3OfFrontPath3 p q r s
    (K.pentagonInnerRightFrontReflPath3 p q r s)

/-- The remaining back-loop contraction also yields the final normalized
right-to-left pentagon comparison directly, without passing through the raw RHS
horn-fill route. -/
private noncomputable def KanComplex.pentagonBigLeftPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s)))
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))) :=
  K.tetrahedronFace2Path3
    (K.pentagonBackComparisonReflPath3 p q r s)
    (K.pentagonLeftBigComparisonTetrahedron p q r s)
    ((K.reflPath3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))).toTetrahedron)

private noncomputable def KanComplex.pentagonBackNormalizationTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
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
  K.pentagonBackNormalizationTetrahedronFromBackContract p q r s
    (K.pentagonBackComparisonReflPath3 p q r s)

private noncomputable def KanComplex.pentagonBoundaryTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonRightBackTriangle p q r s) :=
  K.pentagonBoundaryTetrahedronFromMiddleComparison p q r s
    (K.pentagonBackNormalizationTetrahedron p q r s)

/-- The remaining pentagon bridge is extracted from the final
boundary-normalized tetrahedron. -/
noncomputable def KanComplex.pentagonBridgePath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonRHSRawPath2 p q r s)
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) :=
  K.tetrahedronPath3
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.pentagonBoundaryTetrahedron p q r s)

/-- Pentagon coherence: the 3-cell witnessing that two different ways of
reassociating four consecutive paths are homotopic. This packages the standard
simplicial pentagon filler for the chosen associators. -/
noncomputable def KanComplex.pentagonPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) :=
  K.symmPath3 (K.pentagonBigLeftPath3 p q r s)

namespace StrictKanComplex

private def simplex2Face0Horn (K : StrictKanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (m : K.PathSpace a c) :
    Horn K.toSimplicialSet 1 0 :=
  { missing_le := by omega
    facet := fun i _ => if h1 : i = 1 then m.simplex else p.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hi1 : i = 1 := by omega
      have hj2 : j = 2 := by omega
      subst hi1
      subst hj2
      simp
      exact p.source.trans m.source.symm }

private theorem simplex2_eq_of_face1_face2 (K : StrictKanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {m : K.PathSpace a c}
    {q : K.PathSpace b c} (τ : K.Triangle p m q) {σ : K.Simplex 2}
    (h1 : K.face 1 1 σ = m.simplex) (h2 : K.face 1 2 σ = p.simplex) :
    σ = τ.simplex := by
  let Λ := K.simplex2Face0Horn p m
  have hσ : σ = K.fill Λ := by
    apply K.fill_unique Λ σ
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl
    · simpa [simplex2Face0Horn, Λ] using h1
    · simpa [simplex2Face0Horn, Λ] using h2
  have hτ : τ.simplex = K.fill Λ := by
    apply K.fill_unique Λ τ.simplex
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl
    · simpa [simplex2Face0Horn, Λ] using τ.face1
    · simpa [simplex2Face0Horn, Λ] using τ.face2
  exact hσ.trans hτ.symm

private def simplex3Face0Horn (K : StrictKanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3) :
    Horn K.toSimplicialSet 2 0 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h1 : i = 1 then α.simplex
      else if h2 : i = 2 then τ2.simplex
      else τ3.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h12 | h13 | h23
      · rcases h12 with ⟨rfl, rfl⟩
        calc
          K.face 1 1 τ2.simplex = K.face 1 1 (K.face 2 2 ω.simplex) := by
            rw [ω.face2]
          _ = K.face 1 1 (K.face 2 1 ω.simplex) := by
            simpa using (K.face_face 1 ω.simplex (i := 1) (j := 1) (by omega) (by omega))
          _ = K.face 1 1 (KanComplex.Path2.toTriangle K.toKanComplex α).simplex := by
            rw [ω.face1]
          _ = K.face 1 1 α.simplex := by
            rfl
      · rcases h13 with ⟨rfl, rfl⟩
        calc
          K.face 1 1 τ3.simplex = K.face 1 1 (K.face 2 3 ω.simplex) := by
            rw [ω.face3]
          _ = K.face 1 2 (K.face 2 1 ω.simplex) := by
            simpa using (K.face_face 1 ω.simplex (i := 1) (j := 2) (by omega) (by omega))
          _ = K.face 1 2 (KanComplex.Path2.toTriangle K.toKanComplex α).simplex := by
            rw [ω.face1]
          _ = K.face 1 2 α.simplex := by
            rfl
      · rcases h23 with ⟨rfl, rfl⟩
        calc
          K.face 1 2 τ3.simplex = K.face 1 2 (K.face 2 3 ω.simplex) := by
            rw [ω.face3]
          _ = K.face 1 2 (K.face 2 2 ω.simplex) := by
            simpa using (K.face_face 1 ω.simplex (i := 2) (j := 2) (by omega) (by omega))
          _ = K.face 1 2 τ2.simplex := by rw [ω.face2] }

private theorem simplex3_eq_of_face1_face2_face3 (K : StrictKanComplex)
    {a b c : K.Obj} {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3) {σ : K.Simplex 3}
    (h1 : K.face 2 1 σ = α.simplex)
    (h2 : K.face 2 2 σ = τ2.simplex)
    (h3 : K.face 2 3 σ = τ3.simplex) :
    σ = ω.simplex := by
  let Λ := K.simplex3Face0Horn ω
  have hσ : σ = K.fill Λ := by
    apply K.fill_unique Λ σ
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | hrest
    · simpa [simplex3Face0Horn, Λ] using h1
    · rcases hrest with rfl | rfl
      · simpa [simplex3Face0Horn, Λ] using h2
      · simpa [simplex3Face0Horn, Λ] using h3
  have hω : ω.simplex = K.fill Λ := by
    apply K.fill_unique Λ ω.simplex
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | hrest
    · simpa [simplex3Face0Horn, Λ] using ω.face1
    · rcases hrest with rfl | rfl
      · simpa [simplex3Face0Horn, Λ] using ω.face2
      · simpa [simplex3Face0Horn, Λ] using ω.face3
  exact hσ.trans hω.symm

private theorem path2_eq_of_simplex_eq (K : StrictKanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α β : K.Path2 p q)
    (h : α.simplex = β.simplex) : α = β := by
  cases α
  cases β
  cases h
  simp

/-- In a strict Kan complex, the direct front loop for the remaining right half
of `whiskerLeftWhiskerRight` contracts because its two visible boundary faces
already force it to be the reflexive 2-cell on `reflPath d`. -/
noncomputable def whiskerLeftWhiskerRightMidRightFrontReflPath3 (K : StrictKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
      (K.reflPath2 (K.reflPath d)) := by
  have hFrontSimplex :
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).simplex =
        (K.reflPath2 (K.reflPath d)).simplex := by
    apply K.simplex2_eq_of_face1_face2 ((K.reflPath2 (K.reflPath d)).toTriangle)
    · simpa using (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).face1
    · simpa using (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).face2
  have hFront :
      K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ =
        K.reflPath2 (K.reflPath d) :=
    K.path2_eq_of_simplex_eq
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
      (K.reflPath2 (K.reflPath d))
      hFrontSimplex
  simpa [hFront] using
    (K.reflPath3 (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ))

/-- The remaining right half of `whiskerLeftWhiskerRight` is axiom-free in a
strict Kan complex. -/
noncomputable def whiskerLeftWhiskerRightMidRightPath3 (K : StrictKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.trianglePath2
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
      (K.symmPath2 (K.associatorPath2 α γ δ)) :=
  K.whiskerLeftWhiskerRightMidRightPath3OfFrontPath3 α η δ
    (K.whiskerLeftWhiskerRightMidRightFrontReflPath3 α η δ)

/-- `whiskerLeftWhiskerRight` coherence is axiom-free in a strict Kan complex. -/
noncomputable def whiskerLeftWhiskerRightPath3 (K : StrictKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ)
      (K.transPath2
        (K.associatorPath2 α β δ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
          (K.symmPath2 (K.associatorPath2 α γ δ)))) :=
  K.whiskerLeftWhiskerRightPath3FromTriangleComparison α η δ <|
    K.whiskerLeftWhiskerRightTriangleComparisonFromMidpointRightComparison α η δ <|
      K.whiskerLeftWhiskerRightMidRightPath3 α η δ

/-- In a strict Kan complex, the two pentagon back triangles coincide because
their shared boundary determines a unique Horn[1,0]-filler. -/
private theorem pentagonInnerBackTriangle_simplex_eq_right (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    (K.pentagonInnerBackTriangle p q r s).simplex =
      (K.pentagonRightBackTriangle p q r s).simplex := by
  apply K.simplex2_eq_of_face1_face2 (K.pentagonRightBackTriangle p q r s)
  · simpa using (K.pentagonInnerBackTriangle p q r s).face1
  · simpa using (K.pentagonInnerBackTriangle p q r s).face2

/-- The reduced pentagon front-face obstruction contracts in a strict Kan
complex because the canonical Horn[2,0]-filler is uniquely determined by its
other three faces. -/
noncomputable def pentagonInnerRightFrontReflPath3 (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s))) := by
  let τ := K.pentagonRightBackTriangle p q r s
  let ω := K.reflTriangleTetrahedron τ
  let κ := K.pentagonInnerRightReflCandidateTetrahedron p q r s
  have hτ :
      (K.pentagonInnerBackTriangle p q r s).simplex = τ.simplex :=
    K.pentagonInnerBackTriangle_simplex_eq_right p q r s
  have hκ : κ.simplex = ω.simplex := by
    apply K.simplex3_eq_of_face1_face2_face3 ω
    · simpa [κ] using κ.face1
    · simpa [κ] using κ.face2
    · calc
        K.face 2 3 κ.simplex = (K.pentagonInnerBackTriangle p q r s).simplex := by
          simpa [κ] using κ.face3
        _ = τ.simplex := hτ
  have hFrontSimplex :
      (K.pentagonInnerRightFrontPath2 p q r s).simplex =
        (K.reflPath2 (K.compPath q (K.compPath r s))).simplex := by
    have hFace0 := congrArg (K.face 2 0) hκ
    calc
      (K.pentagonInnerRightFrontPath2 p q r s).simplex
          = K.face 2 0 κ.simplex := by
              symm
              simpa [κ] using κ.face0
      _ = K.face 2 0 ω.simplex := hFace0
      _ = (K.reflPath2 (K.compPath q (K.compPath r s))).simplex := by
            simpa [ω] using ω.face0
  have hFront :
      K.pentagonInnerRightFrontPath2 p q r s =
        K.reflPath2 (K.compPath q (K.compPath r s)) :=
    K.path2_eq_of_simplex_eq
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s)))
      hFrontSimplex
  simpa [hFront] using
    (K.reflPath3 (K.pentagonInnerRightFrontPath2 p q r s))

/-- The old back-comparison loop contracts axiom-free in a strict Kan complex. -/
noncomputable def pentagonBackComparisonReflPath3 (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  K.pentagonBackComparisonReflPath3OfFrontPath3 p q r s
    (K.pentagonInnerRightFrontReflPath3 p q r s)

/-- Pentagon coherence is axiom-free in a strict Kan complex. -/
noncomputable def pentagonPath3 (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) :=
  K.symmPath3 <|
    K.tetrahedronFace2Path3
      (K.pentagonBackComparisonReflPath3 p q r s)
      (K.pentagonLeftBigComparisonTetrahedron p q r s)
      ((K.reflPath3
        (K.transPath2
          (K.associatorPath2 (K.compPath p q) r s)
          (K.associatorPath2 p q (K.compPath r s)))).toTetrahedron)

end StrictKanComplex

/-- The reduced pentagon front-face contraction is axiom-free in a strict
extensional Kan model. -/
noncomputable def StrictExtensionalKanComplex.pentagonInnerRightFrontReflPath3
    (K : StrictExtensionalKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s))) :=
  StrictKanComplex.pentagonInnerRightFrontReflPath3 K.toStrictKanComplex p q r s

/-- The old back-comparison loop is also axiom-free in a strict extensional Kan
model. -/
noncomputable def StrictExtensionalKanComplex.pentagonBackComparisonReflPath3
    (K : StrictExtensionalKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  StrictKanComplex.pentagonBackComparisonReflPath3 K.toStrictKanComplex p q r s

/-- Pentagon coherence is axiom-free in a strict extensional Kan model. -/
noncomputable def StrictExtensionalKanComplex.pentagonPath3
    (K : StrictExtensionalKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) :=
  StrictKanComplex.pentagonPath3 K.toStrictKanComplex p q r s

/-- `whiskerLeftWhiskerRight` specialized to strict extensional Kan models. This
uses the axiom-free strict front-loop contraction rather than the generic open
right-half frontier. -/
noncomputable def StrictExtensionalKanComplex.whiskerLeftWhiskerRightPath3
    (K : StrictExtensionalKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ)
      (K.transPath2
        (K.associatorPath2 α β δ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
          (K.symmPath2 (K.associatorPath2 α γ δ)))) :=
  StrictKanComplex.whiskerLeftWhiskerRightPath3 K.toStrictKanComplex α η δ

/-- `whiskerLeftWhiskerRight` specialized to strict extensional Kan models. This
uses the axiom-free strict front-loop contraction rather than the generic open
right-half frontier. -/
noncomputable def Theory3.strictWhiskerLeftWhiskerRight
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
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
  fun ρ =>
    StrictExtensionalKanComplex.whiskerLeftWhiskerRightPath3 K
      (α ρ) (η ρ) (δ ρ)

/-- Pentagon coherence specialized to strict extensional Kan models. This uses
the axiom-free strict filler-uniqueness proof rather than the generic
front-face axiom. -/
noncomputable def Theory3.strictPentagon
    (K : StrictExtensionalKanComplex)
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
  fun ρ => StrictExtensionalKanComplex.pentagonPath3 K (α ρ) (β ρ) (γ ρ) (δ ρ)

/-- Strict-model wrapper exposing `whiskerLeftWhiskerRight` directly on
interpreted explicit paths and 2-cells. -/
noncomputable def homotopy2_strictWhiskerLeftWhiskerRight_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N}
    (α : Homotopy2 p q) (s : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.whiskerRight K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (homotopy2_in_Theory2 K.toExtensionalKanComplex α))
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerLeft K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (Theory2.whiskerRight K.toExtensionalKanComplex
              (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))))) :=
  Theory3.strictWhiskerLeftWhiskerRight K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

/-- Pentagon coherence at the semantic 3-cell layer. -/
noncomputable def Theory3.pentagon
    (K : ExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.comp K α β) γ δ)
        (Theory2.associator K α β (Theory1.comp K γ δ)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
          (Theory2.associator K α (Theory1.comp K β γ) δ))
        (Theory2.whiskerLeft K α (Theory2.associator K β γ δ))) :=
  fun ρ => K.toReflexiveKanComplex.pentagonPath3 (α ρ) (β ρ) (γ ρ) (δ ρ)

/-- Backward-compatible alias for semantic pentagon coherence. -/
noncomputable def Theory3.pentagonPath3
    (K : ExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.comp K α β) γ δ)
        (Theory2.associator K α β (Theory1.comp K γ δ)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
          (Theory2.associator K α (Theory1.comp K β γ) δ))
        (Theory2.whiskerLeft K α (Theory2.associator K β γ δ))) :=
  Theory3.pentagon K α β γ δ

/-- Pentagon coherence at the HoTFT 3-cell layer. -/
noncomputable def HoTFT3.pentagon
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.comp α β) γ δ)
        (HoTFT2.associator α β (HoTFT1.comp γ δ)))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
          (HoTFT2.associator α (HoTFT1.comp β γ) δ))
        (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ))) :=
  fun K => Theory3.pentagon K (α K) (β K) (γ K) (δ K)

/-- Backward-compatible alias for HoTFT pentagon coherence. -/
noncomputable def HoTFT3.pentagonPath3
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.comp α β) γ δ)
        (HoTFT2.associator α β (HoTFT1.comp γ δ)))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
          (HoTFT2.associator α (HoTFT1.comp β γ) δ))
        (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ))) :=
  HoTFT3.pentagon α β γ δ


/-- Pentagon coherence for interpreted explicit reduction sequences in a fixed
extensional Kan complex. -/
noncomputable def reductionSeq_pentagon_in_Theory3
    (K : ExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
          (reductionSeq_in_Theory1 K r)
          (reductionSeq_in_Theory1 K s))
        (Theory2.associator K
          (reductionSeq_in_Theory1 K p)
          (reductionSeq_in_Theory1 K q)
          (Theory1.comp K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K s))))
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
            (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s)))
        (Theory2.whiskerLeft K
          (reductionSeq_in_Theory1 K p)
          (Theory2.associator K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)
            (reductionSeq_in_Theory1 K s)))) :=
  Theory3.pentagon K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)
    (reductionSeq_in_Theory1 K s)

/-- Strict-model pentagon coherence for interpreted explicit reduction
sequences. This uses the axiom-free strict proof rather than the generic
front-face axiom. -/
noncomputable def reductionSeq_strictPentagon_in_Theory3
    (K : StrictExtensionalKanComplex)
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
  Theory3.strictPentagon K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

set_option maxHeartbeats 1200000

/-- Strict-model source-side normalization for the structural associator shell
when the left explicit path begins with a forward βη step. -/
noncomputable def reductionSeq_associator_source_step_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
          (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
            rest q r))
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
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let βγs := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
  let c1 := reductionSeq_comp_in_Theory2 K0 rest q
  let c2 := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat rest q) r
  let c1s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.step s rest) q
  let c2s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat (ReductionSeq.step s rest) q) r
  let A1 := Theory2.associator K0 α β γ
  let A2 := Theory2.associator K0 α βγs δ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let wrsc1 := Theory2.whiskerRight K0 (Theory2.symm K0 c1) δ
  let αwrsc1 := Theory2.whiskerLeft K0 α wrsc1
  let wrsA1 := Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ
  have hSymmC2s :
      Theory3 K0
        (Theory2.symm K0 c2s)
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.symm K0 A2)) := by
    exact Theory3.trans K0
      (by
        simpa [c2s, A2, c2, α, βγs, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
          reductionSeq_in_Theory1] using
          (Theory3.symmTrans K0 A2 (Theory2.whiskerLeft K0 α c2)))
      (Theory3.transCongrLeft K0
        (Theory3.invWhiskerLeft K0 α c2)
        (Theory2.symm K0 A2))
  have hWrsC1_left :
      Theory3 K0
        (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))) := by
    have hWLWR :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
          (Theory2.trans K0 A2c
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2))) := by
      simpa [A2c, A2, α, β, γ, δ, c1, reductionSeq_in_Theory1] using
        (Theory3.strictWhiskerLeftWhiskerRight K α c1 δ)
    have hSymm0 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))) :=
      Theory3.symmCongr K0 hWLWR
    have hSymm1 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2))))
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))
            (Theory2.symm K0 A2c)) :=
      Theory3.symmTrans K0 A2c
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
          (Theory2.symm K0 A2))
    have hSymm2 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.symm K0 A2))
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
        (Theory2.symm K0 A2)
    have hA2ss :
        Theory3 K0
          (Theory2.symm K0 (Theory2.symm K0 A2))
          A2 :=
      Theory3.symmSymm K0 A2
    have hLeftSymm :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
          (Theory2.whiskerLeft K0 α
            (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))) :=
      Theory3.invWhiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)
    have hRightSymm :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))
          wrsc1 :=
      Theory3.invWhiskerRight K0 c1 δ
    have hInner :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
            (Theory2.symm K0 A2c))
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)) := by
      exact Theory3.trans K0
        (Theory3.transCongrLeft K0 hLeftSymm (Theory2.symm K0 A2c))
        (Theory3.transCongrLeft K0
          (Theory3.whiskerLeftCongr K0 α hRightSymm)
          (Theory2.symm K0 A2c))
    exact Theory3.trans K0 hSymm0
      (Theory3.trans K0 hSymm1
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 hSymm2 (Theory2.symm K0 A2c))
          (Theory3.trans K0
            (Theory3.transAssoc K0
              (Theory2.symm K0 (Theory2.symm K0 A2))
              (Theory2.symm K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
              (Theory2.symm K0 A2c))
            (Theory3.trans K0
              (Theory3.transCongrLeft K0 hA2ss
                (Theory2.trans K0
                  (Theory2.symm K0
                    (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
                  (Theory2.symm K0 A2c)))
              (Theory3.transCongrRight K0 A2 hInner)))))
  have hWrsC1 :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    have h0 :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ)) :=
      Theory3.whiskerRightSymm K0 c1s δ
    have h1 :
        Theory3 K0
          (Theory2.whiskerRight K0 c1s δ)
          (Theory2.trans K0
            (Theory2.whiskerRight K0 A1 δ)
            (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)) := by
      simpa [c1s, A1, c1, α, β, γ, reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1] using
        (Theory3.whiskerRightTrans K0 A1 (Theory2.whiskerLeft K0 α c1) δ)
    have h2 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ))
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))) :=
      Theory3.symmCongr K0 h1
    have h3 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerRight K0 A1 δ)
        (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
    have h4 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.transCongrLeft K0 hWrsC1_left (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
    have h5 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c)
                (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))) := by
      exact Theory3.trans K0
        (Theory3.transAssoc K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
        (Theory3.transCongrRight K0 A2
          (Theory3.transAssoc K0 αwrsc1 (Theory2.symm K0 A2c)
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))
    have h6 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
          wrsA1 :=
      Theory3.invWhiskerRight K0 A1 δ
    exact Theory3.trans K0 h0
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3
          (Theory3.trans K0 h4
            (Theory3.trans K0 h5
              (Theory3.transCongrRight K0 A2
                (Theory3.transCongrRight K0 αwrsc1
                  (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h6)))))))
  have hS0 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 c2s)
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)) :=
    Theory3.transCongrLeft K0 hSymmC2s (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
  have hS1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0
        (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2))
      hWrsC1
  have hCancelA2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2)
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0 αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2) A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2)
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory3.transReflLeft K0
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
  have hS2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    exact Theory3.trans K0
      (Theory3.transAssoc K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.transCongrRight K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) hCancelA2)
  have hCombineSrc :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          αwrsc1)
        (Theory2.whiskerLeft K0 α sourceRest) := by
    simpa [sourceRest, reductionSeq_associator_source_in_Theory2, wrsc1, c2, c1] using
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α (Theory2.symm K0 c2) wrsc1))
  have hS3 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α sourceRest)
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
      (Theory3.transCongrLeft K0 hCombineSrc
        (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))
  simpa [reductionSeq_associator_source_in_Theory2, c1s, c2s, sourceRest, wrsc1, αwrsc1, wrsA1,
    A1, A2, A2c, α, β, γ, δ, βγs, c1, c2, reductionSeq_comp_in_Theory2,
    reductionSeq_in_Theory1, ReductionSeq.concat] using
    (Theory3.trans K0 hS0 (Theory3.trans K0 hS1 (Theory3.trans K0 hS2 hS3)))

/-- Strict-model middle contraction for the forward associator step-head
bridge. -/
noncomputable def reductionSeq_associator_middle_step_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
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
        (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
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
      (Theory3.strictPentagon K α β γ δ)
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

/-- Strict-model forward step-head bridge for the structural associator shell. -/
noncomputable def reductionSeq_comp_associator_stepHead_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
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
    Theory3.transCongrRight K0 assocStep (reductionSeq_associator_target_step_in_Theory3 K0 s rest q r)
  have hMid1 :
      Theory3 K0
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget))
        (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 assocStep A3 αtarget)
  have hMid2 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget)) :=
    Theory3.transCongrRight K0 middlePrefix (Theory3.trans K0 hMid0 hMid1)
  have hMid3 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget))
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 middlePrefix (Theory2.trans K0 assocStep A3) αtarget)
  have hMid4 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget)
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_middle_step_strict_in_Theory3 K s rest q r) αtarget
  have hMid :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.trans K0 hMid2 (Theory3.trans K0 hMid3 hMid4)
  have h0 :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.step s rest) q r)
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep)) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_source_step_strict_in_Theory3 K s rest q r)
      (Theory2.trans K0 assocStep targetStep)
  have h1 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))) :=
    Theory3.transAssoc K0 αsource middlePrefix (Theory2.trans K0 assocStep targetStep)
  have h2 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep)))
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
      (Theory3.whiskerLeftTrans K0 α sourceRest (Theory2.trans K0 assocRest targetRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3 h4)))

/-- Strict-model source-side normalization for the structural associator shell
when the left explicit path begins with an inverse βη step. -/
noncomputable def reductionSeq_associator_source_stepInv_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
          (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
            rest q r))
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
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let βγs := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
  let c1 := reductionSeq_comp_in_Theory2 K0 rest q
  let c2 := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat rest q) r
  let c1s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.stepInv s rest) q
  let c2s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat (ReductionSeq.stepInv s rest) q) r
  let A1 := Theory2.associator K0 α β γ
  let A2 := Theory2.associator K0 α βγs δ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let wrsc1 := Theory2.whiskerRight K0 (Theory2.symm K0 c1) δ
  let αwrsc1 := Theory2.whiskerLeft K0 α wrsc1
  let wrsA1 := Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ
  have hSymmC2s :
      Theory3 K0
        (Theory2.symm K0 c2s)
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.symm K0 A2)) := by
    exact Theory3.trans K0
      (by
        simpa [c2s, A2, c2, α, βγs, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
          reductionSeq_in_Theory1] using
          (Theory3.symmTrans K0 A2 (Theory2.whiskerLeft K0 α c2)))
      (Theory3.transCongrLeft K0
        (Theory3.invWhiskerLeft K0 α c2)
        (Theory2.symm K0 A2))
  have hWrsC1_left :
      Theory3 K0
        (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))) := by
    have hWLWR :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
          (Theory2.trans K0 A2c
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2))) := by
      simpa [A2c, A2, α, β, γ, δ, c1, reductionSeq_in_Theory1] using
        (Theory3.strictWhiskerLeftWhiskerRight K α c1 δ)
    have hSymm0 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))) :=
      Theory3.symmCongr K0 hWLWR
    have hSymm1 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2))))
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))
            (Theory2.symm K0 A2c)) :=
      Theory3.symmTrans K0 A2c
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
          (Theory2.symm K0 A2))
    have hSymm2 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.symm K0 A2))
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
        (Theory2.symm K0 A2)
    have hA2ss :
        Theory3 K0
          (Theory2.symm K0 (Theory2.symm K0 A2))
          A2 :=
      Theory3.symmSymm K0 A2
    have hLeftSymm :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
          (Theory2.whiskerLeft K0 α
            (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))) :=
      Theory3.invWhiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)
    have hRightSymm :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))
          wrsc1 :=
      Theory3.invWhiskerRight K0 c1 δ
    have hInner :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
            (Theory2.symm K0 A2c))
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)) := by
      exact Theory3.trans K0
        (Theory3.transCongrLeft K0 hLeftSymm (Theory2.symm K0 A2c))
        (Theory3.transCongrLeft K0
          (Theory3.whiskerLeftCongr K0 α hRightSymm)
          (Theory2.symm K0 A2c))
    exact Theory3.trans K0 hSymm0
      (Theory3.trans K0 hSymm1
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 hSymm2 (Theory2.symm K0 A2c))
          (Theory3.trans K0
            (Theory3.transAssoc K0
              (Theory2.symm K0 (Theory2.symm K0 A2))
              (Theory2.symm K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
              (Theory2.symm K0 A2c))
            (Theory3.trans K0
              (Theory3.transCongrLeft K0 hA2ss
                (Theory2.trans K0
                  (Theory2.symm K0
                    (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
                  (Theory2.symm K0 A2c)))
              (Theory3.transCongrRight K0 A2 hInner)))))
  have hWrsC1 :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    have h0 :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ)) :=
      Theory3.whiskerRightSymm K0 c1s δ
    have h1 :
        Theory3 K0
          (Theory2.whiskerRight K0 c1s δ)
          (Theory2.trans K0
            (Theory2.whiskerRight K0 A1 δ)
            (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)) := by
      simpa [c1s, A1, c1, α, β, γ, reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1] using
        (Theory3.whiskerRightTrans K0 A1 (Theory2.whiskerLeft K0 α c1) δ)
    have h2 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ))
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))) :=
      Theory3.symmCongr K0 h1
    have h3 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerRight K0 A1 δ)
        (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
    have h4 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.transCongrLeft K0 hWrsC1_left (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
    have h5 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c)
                (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))) := by
      exact Theory3.trans K0
        (Theory3.transAssoc K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
        (Theory3.transCongrRight K0 A2
          (Theory3.transAssoc K0 αwrsc1 (Theory2.symm K0 A2c)
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))
    have h6 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
          wrsA1 :=
      Theory3.invWhiskerRight K0 A1 δ
    exact Theory3.trans K0 h0
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3
          (Theory3.trans K0 h4
            (Theory3.trans K0 h5
              (Theory3.transCongrRight K0 A2
                (Theory3.transCongrRight K0 αwrsc1
                  (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h6)))))))
  have hS0 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 c2s)
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)) :=
    Theory3.transCongrLeft K0 hSymmC2s (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
  have hS1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0
        (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2))
      hWrsC1
  have hCancelA2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2)
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0 αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2) A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2)
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory3.transReflLeft K0
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
  have hS2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    exact Theory3.trans K0
      (Theory3.transAssoc K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.transCongrRight K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) hCancelA2)
  have hCombineSrc :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          αwrsc1)
        (Theory2.whiskerLeft K0 α sourceRest) := by
    simpa [sourceRest, reductionSeq_associator_source_in_Theory2, wrsc1, c2, c1] using
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α (Theory2.symm K0 c2) wrsc1))
  have hS3 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α sourceRest)
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
      (Theory3.transCongrLeft K0 hCombineSrc
        (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))
  simpa [reductionSeq_associator_source_in_Theory2, c1s, c2s, sourceRest, wrsc1, αwrsc1, wrsA1,
    A1, A2, A2c, α, β, γ, δ, βγs, c1, c2, reductionSeq_comp_in_Theory2,
    reductionSeq_in_Theory1, ReductionSeq.concat] using
    (Theory3.trans K0 hS0 (Theory3.trans K0 hS1 (Theory3.trans K0 hS2 hS3)))

/-- Strict-model middle contraction for the inverse associator step-head
bridge. -/
noncomputable def reductionSeq_associator_middle_stepInv_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
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
        (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
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
      (Theory3.strictPentagon K α β γ δ)
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

/-- Strict-model inverse step-head bridge for the structural associator shell. -/
noncomputable def reductionSeq_comp_associator_stepInvHead_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
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
    Theory3.transCongrRight K0 assocStep (reductionSeq_associator_target_stepInv_in_Theory3 K0 s rest q r)
  have hMid1 :
      Theory3 K0
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget))
        (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 assocStep A3 αtarget)
  have hMid2 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget)) :=
    Theory3.transCongrRight K0 middlePrefix (Theory3.trans K0 hMid0 hMid1)
  have hMid3 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget))
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 middlePrefix (Theory2.trans K0 assocStep A3) αtarget)
  have hMid4 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget)
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_middle_stepInv_strict_in_Theory3 K s rest q r) αtarget
  have hMid :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.trans K0 hMid2 (Theory3.trans K0 hMid3 hMid4)
  have h0 :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r)
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep)) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_source_stepInv_strict_in_Theory3 K s rest q r)
      (Theory2.trans K0 assocStep targetStep)
  have h1 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))) :=
    Theory3.transAssoc K0 αsource middlePrefix (Theory2.trans K0 assocStep targetStep)
  have h2 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep)))
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
      (Theory3.whiskerLeftTrans K0 α sourceRest (Theory2.trans K0 assocRest targetRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3 h4)))

/-- In a strict extensional Kan complex, the recursive associator comparison is
fully discharged by the strict forward and inverse step-head bridges. -/
noncomputable def reductionSeq_comp_associator_strict_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc p q r))) :=
  reductionSeq_comp_associator_in_Theory3_of_heads K.toExtensionalKanComplex
    (fun {_ _ _ _ _} s rest q r =>
      reductionSeq_comp_associator_stepHead_strict_in_Theory3 K s rest q r)
    (fun {_ _ _ _ _} s rest q r =>
      reductionSeq_comp_associator_stepInvHead_strict_in_Theory3 K s rest q r)
    p q r

/-- Pentagon coherence for interpreted explicit reduction sequences at the HoTFT
3-cell layer. -/
noncomputable def reductionSeq_pentagon_in_HoTFT3
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
          (reductionSeq_in_HoTFT1 r)
          (reductionSeq_in_HoTFT1 s))
        (HoTFT2.associator
          (reductionSeq_in_HoTFT1 p)
          (reductionSeq_in_HoTFT1 q)
          (HoTFT1.comp (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 s))))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight
            (HoTFT2.associator
              (reductionSeq_in_HoTFT1 p)
              (reductionSeq_in_HoTFT1 q)
              (reductionSeq_in_HoTFT1 r))
            (reductionSeq_in_HoTFT1 s))
          (HoTFT2.associator
            (reductionSeq_in_HoTFT1 p)
            (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))
            (reductionSeq_in_HoTFT1 s)))
        (HoTFT2.whiskerLeft
          (reductionSeq_in_HoTFT1 p)
          (HoTFT2.associator
            (reductionSeq_in_HoTFT1 q)
            (reductionSeq_in_HoTFT1 r)
            (reductionSeq_in_HoTFT1 s)))) :=
  HoTFT3.pentagon
    (reductionSeq_in_HoTFT1 p)
    (reductionSeq_in_HoTFT1 q)
    (reductionSeq_in_HoTFT1 r)
    (reductionSeq_in_HoTFT1 s)


end HigherLambdaModel.Lambda.ExtensionalKan
