/-
# N-Terms and N-Conversions (Section 3)

This module formalizes Section 3 of "The Theory of an Arbitrary Higher λ-Model"
(arXiv:2111.07092), which defines the tower of n-terms and n-conversions.

## Key Definitions

- **Definition 3.1**: n-conversion (Σₙ) - the set of n-conversions between (n-1)-conversions
- **Definition 3.2**: TH_λ= - the classical λ-theory of βη-equivalence
- **Definition 3.3**: n-terms (Πₙ) - higher λ-abstractions representing n-cells
- **Proposition 3.4**: Πₙ ⊆ Σₙ - every n-term induces an n-conversion

## The Key Insight

The paper's central contribution is showing that:
1. The higher structure of λ-calculus (n-conversions) arises naturally
2. This structure can be captured by "n-terms" (higher λ-abstractions)
3. In any extensional Kan complex, Πₙ ⊆ Σₙ
4. Therefore TH_λ= ⊆ HoTFT

## References

- Martínez-Rivillas & de Queiroz, "The Theory of an Arbitrary Higher λ-Model"
-/

import HigherLambdaModel.Lambda.Reduction
import HigherLambdaModel.Lambda.HigherTerms
import HigherLambdaModel.Lambda.ExtensionalKan

namespace HigherLambdaModel.Lambda.NTerms

open Term ExtensionalKan HigherTerms

/-! ## N-Conversions (Definition 3.1)

The tower of n-conversions captures the higher structure of βη-equivalence:
- Σ₀ = λ-terms (the 0-cells)
- Σ₁ = βη-conversions between terms (1-cells)
- Σ₂ = proofs that two βη-conversions are equal (2-cells)
- Σₙ₊₁ = higher cells generated recursively from lower ones -/

/-- The type of n-conversions.

    Σ₀ = Term (λ-terms)
    Σ₁ = pairs of terms with a reduction sequence (1-conversions)
    Σ₂ = homotopies between parallel reduction sequences (2-conversions)
    Σₙ for n ≥ 3 = recursively generated higher cells from `HigherTerms.Cell`.

    We use the same constructive tower as the core higher-terms layer, rather
    than collapsing higher dimensions to a terminal type. -/
abbrev NConversion : Nat → Sort _ := HigherTerms.Cell

/-- The immediate source boundary of an `n+1`-conversion. -/
def NConversion.source : {n : Nat} → NConversion (n + 1) → NConversion n :=
  HigherTerms.Cell.source

/-- The immediate target boundary of an `n+1`-conversion. -/
def NConversion.target : {n : Nat} → NConversion (n + 1) → NConversion n :=
  HigherTerms.Cell.target

/-- Generic source globularity for the recursive higher-conversion tower. -/
theorem NConversion.globular_src {n : Nat} (f : NConversion (n + 2)) :
    NConversion.source (NConversion.source f) =
    NConversion.source (NConversion.target f) :=
  HigherTerms.Cell.globular_source f

/-- Generic target globularity for the recursive higher-conversion tower. -/
theorem NConversion.globular_tgt {n : Nat} (f : NConversion (n + 2)) :
    NConversion.target (NConversion.source f) =
    NConversion.target (NConversion.target f) :=
  HigherTerms.Cell.globular_target f

/-- The source of a 1-conversion. -/
abbrev NConversion.source0 : NConversion 1 → NConversion 0 :=
  NConversion.source (n := 0)

/-- The source of a 2-conversion. -/
abbrev NConversion.source1 : NConversion 2 → NConversion 1 :=
  NConversion.source (n := 1)

/-- The target of an n-conversion -/
abbrev NConversion.target0 : NConversion 1 → NConversion 0 :=
  NConversion.target (n := 0)

/-- The target of a 2-conversion. -/
abbrev NConversion.target1 : NConversion 2 → NConversion 1 :=
  NConversion.target (n := 1)

/-! ## TH_λ= : The Classical λ-Theory (Definition 3.2)

TH_λ= is the set of all βη-equivalent term pairs.
This is the "propositionally truncated" view of λ-calculus equality. -/

/-- TH_λ= : The theory of βη-equivalence.
    Two terms are in TH_λ= if they are βη-convertible. -/
def TH_lambda_eq (M N : Term) : Prop :=
  BetaEtaConv M N

/-- Notation for membership in TH_λ= -/
scoped notation:50 M " =_TH " N => TH_lambda_eq M N

/-! ## N-Terms (Definition 3.3)

N-terms are "computational" representatives of n-conversions.
The key idea is that while an n-conversion is an abstract equivalence,
an n-term is a concrete computational object that witnesses it.

- Π₀ = λ-terms (the 0-terms)
- Π₁ = "higher λ-abstractions" λ¹r.h(r) witnessing βη-equivalences
- Π₂ = 2-dimensional λ-abstractions
- etc.

The construction uses the fact that reduction sequences are explicit
computational paths, not just existence proofs. -/

/-- Well-formed 1-terms indexed by source and target.

    This indexed definition ensures well-formedness by construction:
    - `seq` can only compose terms where the target of the first matches
      the source of the second (enforced by the type indices)
    - No runtime checks or axioms needed -/
inductive NTerm1 : Term → Term → Type where
  /-- A single reduction step from M to N -/
  | redex : BetaEtaStep M N → NTerm1 M N
  /-- Composition of two 1-terms: the intermediate term P is shared -/
  | seq : NTerm1 M P → NTerm1 P N → NTerm1 M N
  /-- Identity/reflexivity: trivial path from M to M -/
  | refl : NTerm1 M M

/-- Convert a well-formed 1-term (NTerm1) to a reduction sequence -/
def NTerm1.toReductionSeq : NTerm1 M N → ReductionSeq M N
  | .redex s => ReductionSeq.single s
  | .seq t₁ t₂ => ReductionSeq.concat t₁.toReductionSeq t₂.toReductionSeq
  | .refl => ReductionSeq.refl _

/-- An n-term is an explicit computational witness for an n-conversion.

    For n = 0: Just a λ-term
    For n = 1: A well-formed 1-term (indexed by source and target)
    For n = 2: A Church-Rosser diamond witnessing a homotopy
    For n ≥ 3: An explicit higher conversion from the recursive tower -/
inductive NTerm : Nat → Type where
  /-- A 0-term is just a λ-term -/
  | term : Term → NTerm 0
  /-- A 1-term packaged with its source and target -/
  | nterm1 : (M N : Term) → NTerm1 M N → NTerm 1
  /-- A 2-term from Church-Rosser -/
  | diamond : (M N₁ N₂ P : Term) →
              ReductionSeq M N₁ → ReductionSeq M N₂ →
              ReductionSeq N₁ P → ReductionSeq N₂ P →
              NTerm 2
  /-- Identity 2-term -/
  | refl2 : {M N : Term} → ReductionSeq M N → NTerm 2
  /-- Higher terms reuse the constructive higher-conversion tower directly. -/
  | liftHigher : {n : Nat} → NConversion (n + 3) → NTerm (n + 3)

namespace NTerm

/-- Extract the underlying term from a 0-term -/
def toTerm : NTerm 0 → Term
  | term t => t

/-- The source term of a 1-term -/
def source1 : NTerm 1 → Term
  | nterm1 M _ _ => M

/-- The target term of a 1-term -/
def target1 : NTerm 1 → Term
  | nterm1 _ N _ => N

/-- Extract the inner NTerm1 from an NTerm 1 -/
def inner1 : (t : NTerm 1) → NTerm1 t.source1 t.target1
  | nterm1 _ _ t => t

/-- Smart constructor: create a 1-term from a single step -/
def redex (M N : Term) (h : BetaEtaStep M N) : NTerm 1 :=
  nterm1 M N (NTerm1.redex h)

/-- Smart constructor: compose two 1-terms -/
def seq (t₁ t₂ : NTerm 1) (h : t₁.target1 = t₂.source1) : NTerm 1 :=
  nterm1 t₁.source1 t₂.target1 (NTerm1.seq t₁.inner1 (h ▸ t₂.inner1))

/-- Smart constructor: reflexivity 1-term -/
def refl1 (M : Term) : NTerm 1 :=
  nterm1 M M NTerm1.refl

/-- Well-formedness is proved constructively for the `seq` smart constructor. -/
theorem seq_well_formed (t₁ t₂ : NTerm 1) (h : t₁.target1 = t₂.source1) :
    (seq t₁ t₂ h).source1 = t₁.source1 ∧ (seq t₁ t₂ h).target1 = t₂.target1 :=
  ⟨rfl, rfl⟩

/-- Convert a 1-term to a reduction sequence -/
def toReductionSeq : NTerm 1 → Σ (M N : Term), ReductionSeq M N
  | nterm1 M N t => ⟨M, N, t.toReductionSeq⟩

end NTerm

/-! ## The Embedding Πₙ → Σₙ (Proposition 3.4)

Every n-term induces an n-conversion. This is the key result that
shows the computational content of n-terms is captured by n-conversions. -/

/-- Embed an n-term into the corresponding n-conversion -/
def NTerm.toNConversion : {n : Nat} → NTerm n → NConversion n
  | 0, NTerm.term t => t
  | 1, NTerm.nterm1 M N t => ⟨M, N, t.toReductionSeq⟩
  | 2, NTerm.diamond M _ _ P p₁ p₂ q₁ q₂ =>
    ⟨M, P, ReductionSeq.concat p₁ q₁, ReductionSeq.concat p₂ q₂, Homotopy2.ofDiamond p₁ p₂ q₁ q₂⟩
  | 2, NTerm.refl2 p => ⟨_, _, p, p, Homotopy2.refl p⟩
  | _ + 3, NTerm.liftHigher c => c

/-! ## Higher λ-Abstraction (λⁿ)

The paper introduces "higher λ-abstraction" λⁿr.h(r) as a way to
construct n-terms. This is the computational analog of taking
a dependent function type in HoTT.

For n = 1: λ¹r.h(r) constructs a 1-term from a reduction context
For n = 2: λ²r.h(r) constructs a 2-term from a homotopy context -/

/-- A 1-context is a term with a hole that can be filled -/
structure Context1 where
  /-- The context as a function from terms to terms -/
  ctx : Term → Term
  /-- The context preserves reduction (congruence) -/
  preserves_reduction : ∀ M N, BetaEtaStep M N → BetaEtaStep (ctx M) (ctx N)

/-- Higher λ-abstraction at level 1: λ¹r.C[r] -/
def higherLam1 (C : Context1) (M N : Term) (h : BetaEtaStep M N) : NTerm 1 :=
  NTerm.redex (C.ctx M) (C.ctx N) (C.preserves_reduction M N h)

/-! ### Primitive λ¹-terms for β₁ and η₁ (Proposition 3.2) -/

/-- The primitive λ¹-term witnessing the root β-contraction. This is the base
case of Proposition 3.2 showing that β₁ is itself a λ¹-term. -/
def beta1Term (M N : Term) : NTerm 1 :=
  NTerm.redex (Term.app (Term.lam M) N) (M[N])
    (BetaEtaStep.beta (BetaStep.beta M N))

/-- The primitive λ¹-term witnessing the raw η-contraction
`λ.(M · 0) → shift (-1) 0 M` when variable `0` is not free in `M`.
This is the base case of Proposition 3.2 showing that η₁ is a λ¹-term. -/
def eta1Term (M : Term) (h : Term.hasFreeVar 0 M = false) : NTerm 1 :=
  NTerm.redex (Term.lam (Term.app M (Term.var 0))) (Term.shift (-1) 0 M)
    (BetaEtaStep.eta (EtaStep.eta M (by
      intro htrue
      rw [h] at htrue
      cases htrue)))

/-! ## Interpretation of N-Terms in Extensional Kan Complexes

The semantic justification: in any extensional Kan complex K,
an n-term denotes an n-cell in K. -/

/-- Interpret a 0-term in an extensional Kan complex -/
noncomputable def interpretNTerm0 (K : ExtensionalKanComplex)
    (ρ : Valuation K.toReflexiveKanComplex) : NTerm 0 → K.Obj
  | NTerm.term t => interpret K.toReflexiveKanComplex ρ t

/-! ## Helper Lemmas for Interpretation and Shifting -/

/-- When a term M has no free variable 0, interpreting M under an extended valuation
    equals interpreting shift (-1) 0 M under the original valuation.

    This is a key lemma for proving η-soundness. Intuitively: if M doesn't use variable 0,
    then ⟦M⟧ρ' (where ρ' extends ρ with a value at position 0) equals ⟦M'⟧ρ where M' is M
    with all its variable indices decremented (since they all referred to the outer context).

    This is now proven in ExtensionalKan.lean via interpret_unshift_aux. -/
theorem interpret_unshift' (K : ReflexiveKanComplex) (M : Term) (ρ : Valuation K) (f : K.Obj)
    (h : Term.hasFreeVar 0 M = false) :
    interpret K (fun n => if n = 0 then f else ρ (n - 1)) M =
    interpret K ρ (Term.shift (-1) 0 M) :=
  ExtensionalKan.interpret_unshift K M ρ f h

/-- Soundness of a single β-step in an extensional Kan complex.
    This proves that β-reduction preserves interpretation. -/
theorem betaStep_sound (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N :=
  ExtensionalKan.betaStep_sound K M N h ρ

/-- Soundness of a single η-step in an extensional Kan complex.
    This proves that η-reduction preserves interpretation. -/
theorem etaStep_sound (K : ExtensionalKanComplex) (M N : Term)
    (h : EtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N :=
  ExtensionalKan.etaStep_sound K M N h ρ

/-- Soundness of a single βη-step in an extensional Kan complex.

    This is a fundamental soundness theorem for the interpretation of λ-terms
    in extensional Kan complexes. The proof works by case analysis on whether
    the step is a β-step or η-step, and then uses the corresponding soundness theorem. -/
theorem betaEtaStep_sound (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaEtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N :=
  ExtensionalKan.betaEtaStep_sound K M N h ρ

/-- Structural proof-relevant interpretation of an indexed 1-term in a fixed
extensional Kan complex. -/
noncomputable def nterm1_indexed_in_Theory1 (K : ExtensionalKanComplex) :
    {M N : Term} → NTerm1 M N → Theory1 K M N
  | _, _, .redex s =>
      ExtensionalKan.betaEtaStep_in_Theory1 K _ _ s
  | _, _, .seq t₁ t₂ =>
      Theory1.comp K (nterm1_indexed_in_Theory1 K t₁) (nterm1_indexed_in_Theory1 K t₂)
  | M, _, .refl =>
      fun ρ => K.reflPath (interpret K.toReflexiveKanComplex ρ M)

/-- Structural proof-relevant interpretation of an indexed 1-term in HoTFT. -/
noncomputable def nterm1_indexed_in_HoTFT1 {M N : Term} (t : NTerm1 M N) :
    HoTFT1 M N :=
  fun K => nterm1_indexed_in_Theory1 K t

/-- Structural proof-relevant interpretation of a packaged 1-term in a fixed
extensional Kan complex. -/
noncomputable def nterm1_in_Theory1 (K : ExtensionalKanComplex) (t : NTerm 1) :
    Theory1 K t.source1 t.target1 := by
  cases t with
  | nterm1 M N inner =>
      exact nterm1_indexed_in_Theory1 K inner

/-- Structural proof-relevant interpretation of a packaged 1-term in HoTFT. -/
noncomputable def nterm1_in_HoTFT1 (t : NTerm 1) : HoTFT1 t.source1 t.target1 :=
  fun K => nterm1_in_Theory1 K t

/-- Interpret a 1-term in a fixed extensional Kan complex.

This is the low-dimensional instance of Proposition 3.3 saying that the model's
1-simplex space carries the semantics of λ¹-terms. -/
noncomputable def interpretNTerm1 (K : ExtensionalKanComplex) (t : NTerm 1) :
    Theory1 K t.source1 t.target1 :=
  nterm1_in_Theory1 K t

/-- Higher λ-abstraction at level 1 denotes a semantic 1-cell in every fixed
extensional Kan complex. -/
noncomputable def higherLam1_in_Theory1 (K : ExtensionalKanComplex)
    (C : Context1) (M N : Term) (h : BetaEtaStep M N) :
    Theory1 K (C.ctx M) (C.ctx N) :=
  interpretNTerm1 K (higherLam1 C M N h)

/-- Higher λ-abstraction at level 1 denotes a proof-relevant HoTFT 1-cell. -/
noncomputable def higherLam1_in_HoTFT1
    (C : Context1) (M N : Term) (h : BetaEtaStep M N) :
    HoTFT1 (C.ctx M) (C.ctx N) :=
  nterm1_in_HoTFT1 (higherLam1 C M N h)

/-- The primitive β₁-term denotes a semantic 1-cell in any fixed extensional
Kan complex. -/
noncomputable def beta1Term_in_Theory1 (K : ExtensionalKanComplex) (M N : Term) :
    Theory1 K (Term.app (Term.lam M) N) (M[N]) :=
  interpretNTerm1 K (beta1Term M N)

/-- The primitive β₁-term denotes a proof-relevant HoTFT 1-cell. -/
noncomputable def beta1Term_in_HoTFT1 (M N : Term) :
    HoTFT1 (Term.app (Term.lam M) N) (M[N]) :=
  nterm1_in_HoTFT1 (beta1Term M N)

/-- The primitive η₁-term denotes a semantic 1-cell in any fixed extensional
Kan complex. -/
noncomputable def eta1Term_in_Theory1 (K : ExtensionalKanComplex)
    (M : Term) (h : Term.hasFreeVar 0 M = false) :
    Theory1 K (Term.lam (Term.app M (Term.var 0))) (Term.shift (-1) 0 M) :=
  interpretNTerm1 K (eta1Term M h)

/-- The primitive η₁-term denotes a proof-relevant HoTFT 1-cell. -/
noncomputable def eta1Term_in_HoTFT1
    (M : Term) (h : Term.hasFreeVar 0 M = false) :
    HoTFT1 (Term.lam (Term.app M (Term.var 0))) (Term.shift (-1) 0 M) :=
  nterm1_in_HoTFT1 (eta1Term M h)

/-- Soundness for the indexed NTerm1 type -/
theorem nterm1_indexed_sound (K : ExtensionalKanComplex) {M N : Term} (t : NTerm1 M N)
    (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N :=
  ExtensionalKan.reductionSeq_sound K t.toReductionSeq ρ

/-- Two terms related by a 1-term have equal interpretations -/
theorem nterm1_sound (K : ExtensionalKanComplex) (t : NTerm 1)
    (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ t.source1 =
    interpret K.toReflexiveKanComplex ρ t.target1 := by
  match t with
  | NTerm.nterm1 M N inner =>
    simp only [NTerm.source1, NTerm.target1]
    exact nterm1_indexed_sound K inner ρ

/-! ## Main Results

### Proposition 3.4: Πₙ ⊆ Σₙ

Every n-term induces an n-conversion. We've already defined this as
`NTerm.toNConversion`. The inclusion is given by construction. -/

/-- Every n-term embeds into the corresponding n-conversion (Proposition 3.4).

    Πₙ ⊆ Σₙ : Every computational witness (n-term) induces an abstract
    equivalence (n-conversion). This is the key result connecting the
    "computational" view (explicit reduction sequences) with the
    "propositional" view (mere existence of equivalence). -/
def pi_subset_sigma (n : Nat) (t : NTerm n) : NConversion n :=
  t.toNConversion

/-! ### Corollary: TH_λ= ⊆ HoTFT

Any equation provable in the classical λ-theory TH_λ= is also
valid in HoTFT (the intersection of all extensional Kan complex theories). -/

/-- **Main Theorem**: TH_λ= ⊆ HoTFT (Corollary to Proposition 3.4)

    If M =βη N in the classical λ-theory (i.e., M and N are βη-convertible),
    then M = N in the Homotopy Type-Free Theory (i.e., M and N have equal
    interpretations in ALL extensional Kan complexes).

    **Significance**: This theorem establishes that classical λ-calculus
    embeds faithfully into homotopic λ-models. The higher structure of
    homotopic models is a conservative extension of classical βη-equivalence.

    **Proof**: By induction on the βη-conversion relation, using:
    - `betaEtaStep_sound` for forward steps
    - Symmetry of equality for inverse steps -/
theorem TH_lambda_eq_subset_HoTFT (M N : Term) (h : M =_TH N) :
    HoTFT_eq M N := by
  exact ExtensionalKan.reductionSeq_in_HoTFT (ReductionSeq.ofBetaEtaConv h)

/-- Proof-relevant version of the main theorem: a classical βη-conversion
induces a semantic 1-conversion in every extensional Kan complex. -/
noncomputable def TH_lambda_eq_subset_HoTFT1 (M N : Term) (h : M =_TH N) :
    HoTFT1 M N :=
  ExtensionalKan.reductionSeq_in_HoTFT1 (ReductionSeq.ofBetaEtaConv h)

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
proof-relevant semantic HoTFT 2-conversion between the corresponding
structural semantic 1-cells, provided the 2-cell lies in the fragment already
supported by the simplicial semantics. -/
noncomputable def StructuralHomotopy2_subset_HoTFT2
    {M N : Term} {p q : ReductionSeq M N} (α : StructuralHomotopy2 p q) :
    HoTFT2 (ExtensionalKan.reductionSeq_in_HoTFT1 p)
      (ExtensionalKan.reductionSeq_in_HoTFT1 q) :=
  ExtensionalKan.structuralHomotopy2_in_HoTFT2 α

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
proof-relevant semantic HoTFT 2-conversion between the corresponding semantic
1-cells. The resulting semantic witness is an actual simplicial 2-cell in each
model and now lands directly on the structural HoTFT 1-cells induced by the
boundary reduction sequences. -/
noncomputable def Homotopy2_subset_HoTFT2
    {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT2 (ExtensionalKan.reductionSeq_in_HoTFT1 p)
      (ExtensionalKan.reductionSeq_in_HoTFT1 q) :=
  ExtensionalKan.homotopy2_in_HoTFT2 α

/-- Every explicit syntactic 2-cell admits a reflexive semantic HoTFT 3-cell
over its interpreted HoTFT 2-cell. -/
noncomputable def Homotopy2_refl_subset_HoTFT3
    {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3 (ExtensionalKan.homotopy2_in_HoTFT2 α)
      (ExtensionalKan.homotopy2_in_HoTFT2 α) :=
  ExtensionalKan.homotopy2_refl_in_HoTFT3 α

/-- Equality of explicit syntactic 2-cells induces a semantic HoTFT 3-cell
between their interpreted HoTFT 2-cells. -/
noncomputable def Homotopy2_eq_subset_HoTFT3
    {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q} (h : α = β) :
    HoTFT3 (ExtensionalKan.homotopy2_in_HoTFT2 α)
      (ExtensionalKan.homotopy2_in_HoTFT2 β) :=
  ExtensionalKan.homotopy2_eq_in_HoTFT3 h

/-- Every structurally supported syntactic 3-cell between parallel explicit
2-cells induces a proof-relevant semantic HoTFT 3-conversion. -/
noncomputable def StructuralHomotopy3_subset_HoTFT3
    {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q}
    (η : HigherLambdaModel.Lambda.HigherTerms.StructuralHomotopy3 α β) :
    HoTFT3 (ExtensionalKan.homotopy2_in_HoTFT2 α)
      (ExtensionalKan.homotopy2_in_HoTFT2 β) :=
  ExtensionalKan.structuralHomotopy3_in_HoTFT3 η

/-- Every explicit syntactic 2-cell admits a reflexive semantic HoTFT 4-cell
over the reflexive semantic HoTFT 3-cell on its interpreted HoTFT 2-cell. -/
noncomputable def Homotopy2_refl_subset_HoTFT4
    {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT4 (ExtensionalKan.homotopy2_refl_in_HoTFT3 α)
      (ExtensionalKan.homotopy2_refl_in_HoTFT3 α) :=
  HoTFT4.refl (ExtensionalKan.homotopy2_refl_in_HoTFT3 α)

/-- Every structurally supported syntactic 3-cell admits a reflexive semantic
HoTFT 4-cell over its interpreted HoTFT 3-cell. -/
noncomputable def StructuralHomotopy3_refl_subset_HoTFT4
    {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q}
    (η : HigherLambdaModel.Lambda.HigherTerms.StructuralHomotopy3 α β) :
    HoTFT4 (StructuralHomotopy3_subset_HoTFT3 η)
      (StructuralHomotopy3_subset_HoTFT3 η) :=
  HoTFT4.refl (StructuralHomotopy3_subset_HoTFT3 η)

/-- The semantic image of syntactic interchange is already a HoTFT 3-cell in
the current simplicial 3-cell layer. -/
noncomputable def Homotopy2_interchange_subset_HoTFT3
    {L M N : Term} {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HoTFT3
      (HoTFT2.hcomp (ExtensionalKan.homotopy2_in_HoTFT2 α)
        (ExtensionalKan.homotopy2_in_HoTFT2 β))
      (HoTFT2.trans
        (HoTFT2.whiskerRight (ExtensionalKan.homotopy2_in_HoTFT2 α)
          (ExtensionalKan.reductionSeq_in_HoTFT1 q))
        (HoTFT2.whiskerLeft (ExtensionalKan.reductionSeq_in_HoTFT1 p')
          (ExtensionalKan.homotopy2_in_HoTFT2 β))) :=
  ExtensionalKan.homotopy2_interchange_in_HoTFT3 α β

/-- The interpreted structural associator carries a boundary-aware HoTFT
tetrahedron witness. -/
noncomputable def ReductionSeq_associator_subset_HoTFTTetrahedron
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 q)
            (ExtensionalKan.reductionSeq_in_HoTFT1 r))))
      (HoTFT2.toTriangle (ExtensionalKan.reductionSeq_associator_in_HoTFT2 p q r))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 q)
          (ExtensionalKan.reductionSeq_in_HoTFT1 r)))
      (HoTFT1.assocTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (ExtensionalKan.reductionSeq_in_HoTFT1 q)
        (ExtensionalKan.reductionSeq_in_HoTFT1 r)) :=
  ExtensionalKan.reductionSeq_associator_in_HoTFTTetrahedron p q r

/-- Degenerating the semantic composition triangle yields the boundary-aware
tetrahedron for reflexivity on a semantic composite. -/
noncomputable def ReductionSeq_comp_refl_subset_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 q)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 p)
            (ExtensionalKan.reductionSeq_in_HoTFT1 q))))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (ExtensionalKan.reductionSeq_in_HoTFT1 q))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (ExtensionalKan.reductionSeq_in_HoTFT1 q)) :=
  ExtensionalKan.reductionSeq_comp_refl_in_HoTFTTetrahedron p q

/-- The interpreted structural left unitor carries a boundary-aware HoTFT
tetrahedron witness. -/
noncomputable def ReductionSeq_leftUnitor_subset_HoTFTTetrahedron
    {M N : Term} (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p)))
      (HoTFT2.toTriangle (ExtensionalKan.reductionSeq_leftUnitor_in_HoTFT2 p))
      (HoTFT1.sourceDegenerateTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p))
      (HoTFT1.compTriangle (HoTFT1.refl M) (ExtensionalKan.reductionSeq_in_HoTFT1 p)) :=
  ExtensionalKan.reductionSeq_leftUnitor_in_HoTFTTetrahedron p

/-- The interpreted structural right unitor carries a boundary-aware HoTFT
tetrahedron witness. -/
noncomputable def ReductionSeq_rightUnitor_subset_HoTFTTetrahedron
    {M N : Term} (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle (ExtensionalKan.reductionSeq_rightUnitor_in_HoTFT2 p))
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p)))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p) (HoTFT1.refl N)) :=
  ExtensionalKan.reductionSeq_rightUnitor_in_HoTFTTetrahedron p

/-- Left whiskering of an interpreted explicit 2-cell carries a boundary-aware
HoTFT tetrahedron witness. -/
noncomputable def Homotopy2_whiskerLeft_subset_HoTFTTetrahedron
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (ExtensionalKan.homotopy2_in_HoTFT2 α))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerLeft (ExtensionalKan.reductionSeq_in_HoTFT1 r)
          (ExtensionalKan.homotopy2_in_HoTFT2 α)))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (ExtensionalKan.reductionSeq_in_HoTFT1 q))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (ExtensionalKan.reductionSeq_in_HoTFT1 p)) :=
  ExtensionalKan.homotopy2_whiskerLeft_in_HoTFTTetrahedron r α

/-- The source-side boundary-aware tetrahedron for the `whiskerLeftRefl`
constructor. -/
noncomputable def Homotopy2_whiskerLeftRefl_source_subset_HoTFTTetrahedron
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerLeft (ExtensionalKan.reductionSeq_in_HoTFT1 r)
          (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p))))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (ExtensionalKan.reductionSeq_in_HoTFT1 p))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (ExtensionalKan.reductionSeq_in_HoTFT1 p)) :=
  Homotopy2_whiskerLeft_subset_HoTFTTetrahedron r (Homotopy2.refl p)

/-- The intermediate target-side boundary-aware tetrahedron for the
`whiskerLeftRefl` constructor. It has the same outer boundary as the
source-side witness and lands on the reflexive 2-cell of the semantic
composite. -/
noncomputable def Homotopy2_whiskerLeftRefl_target_subset_HoTFTTetrahedron
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 r)
            (ExtensionalKan.reductionSeq_in_HoTFT1 p))))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (ExtensionalKan.reductionSeq_in_HoTFT1 p))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (ExtensionalKan.reductionSeq_in_HoTFT1 p)) :=
  ReductionSeq_comp_refl_subset_HoTFTTetrahedron r p

/-- Left whiskering preserves reflexive 2-cells up to a proof-relevant HoTFT
3-cell. This is the first normalization obtained from the new tetrahedron
comparison layer. -/
noncomputable def Homotopy2_whiskerLeftRefl_subset_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerLeft (ExtensionalKan.reductionSeq_in_HoTFT1 r)
        (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p)))
      (HoTFT2.refl
        (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 r)
          (ExtensionalKan.reductionSeq_in_HoTFT1 p))) :=
  ExtensionalKan.homotopy2_whiskerLeftRefl_in_HoTFT3 r p

/-- Right whiskering of an interpreted explicit 2-cell carries a boundary-aware
HoTFT tetrahedron witness. -/
noncomputable def Homotopy2_whiskerRight_subset_HoTFTTetrahedron
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight (ExtensionalKan.homotopy2_in_HoTFT2 α)
          (ExtensionalKan.reductionSeq_in_HoTFT1 s)))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 q)
        (ExtensionalKan.reductionSeq_in_HoTFT1 s))
      (HoTFT1.whiskerRightTriangle (ExtensionalKan.homotopy2_in_HoTFT2 α)
        (ExtensionalKan.reductionSeq_in_HoTFT1 s)) :=
  ExtensionalKan.homotopy2_whiskerRight_in_HoTFTTetrahedron α s

/-- The source-side boundary-aware tetrahedron for the `whiskerRightRefl`
constructor. -/
noncomputable def Homotopy2_whiskerRightRefl_source_subset_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p))
          (ExtensionalKan.reductionSeq_in_HoTFT1 s)))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (ExtensionalKan.reductionSeq_in_HoTFT1 s))
      (HoTFT1.whiskerRightTriangle
        (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p))
        (ExtensionalKan.reductionSeq_in_HoTFT1 s)) :=
  Homotopy2_whiskerRight_subset_HoTFTTetrahedron (Homotopy2.refl p) s

/-- The intermediate reflexive target tetrahedron on the semantic composite
that the `whiskerRightRefl` constructor aims to normalize toward. -/
noncomputable def Homotopy2_whiskerRightRefl_target_subset_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 p)
            (ExtensionalKan.reductionSeq_in_HoTFT1 s))))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (ExtensionalKan.reductionSeq_in_HoTFT1 s))
      (HoTFT1.compTriangle (ExtensionalKan.reductionSeq_in_HoTFT1 p)
        (ExtensionalKan.reductionSeq_in_HoTFT1 s)) :=
  ReductionSeq_comp_refl_subset_HoTFTTetrahedron p s

/-- A first boundary-aware 4-simplex comparison for `whiskerRightRefl`. This
matches the source and target tetrahedra by inserting one extra boundary face;
the remaining gap is only the final normalization into `HoTFT3`. -/
noncomputable def Homotopy2_whiskerRightRefl_subset_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (ExtensionalKan.reductionSeq_in_HoTFT1 p)
            (ExtensionalKan.reductionSeq_in_HoTFT1 s))))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p))
          (ExtensionalKan.reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (ExtensionalKan.reductionSeq_in_HoTFT1 p))
          (ExtensionalKan.reductionSeq_in_HoTFT1 s))) :=
  ExtensionalKan.homotopy2_whiskerRightRefl_in_HoTFTTetrahedron p s

/-- Every computational 2-term packages a semantic HoTFT 2-conversion between
the semantic 1-cells induced by its boundary reduction sequences. -/
noncomputable def interpretNTerm2 (K : ExtensionalKanComplex) (t : NTerm 2) :
    Σ (M N : Term) (α β : Theory1 K M N), Theory2 K α β := by
  rcases t.toNConversion with ⟨M, N, p, q, h2⟩
  exact ⟨M, N, ExtensionalKan.reductionSeq_in_Theory1 K p,
    ExtensionalKan.reductionSeq_in_Theory1 K q,
    ExtensionalKan.homotopy2_in_Theory2 K h2⟩

/-- Every computational 2-term packages a proof-relevant semantic HoTFT
2-conversion between the semantic 1-cells induced by its boundary reduction
sequences. -/
noncomputable def NTerm2_subset_HoTFT2 (t : NTerm 2) :
    Σ (M N : Term) (α β : HoTFT1 M N), HoTFT2 α β := by
  rcases t.toNConversion with ⟨M, N, p, q, h2⟩
  exact ⟨M, N, ExtensionalKan.reductionSeq_in_HoTFT1 p,
    ExtensionalKan.reductionSeq_in_HoTFT1 q,
    ExtensionalKan.homotopy2_in_HoTFT2 h2⟩

/-- HoTFT-level interpretation wrapper for computational 2-terms. -/
noncomputable def interpretNTerm2_in_HoTFT2 (t : NTerm 2) :
    Σ (M N : Term) (α β : HoTFT1 M N), HoTFT2 α β :=
  NTerm2_subset_HoTFT2 t

/-! ## The Full Tower: Weak ω-Groupoid Structure

The paper shows that the tower (Σ₀, Σ₁, Σ₂, ...) forms a weak ω-groupoid.
We characterize the low-dimensional structure explicitly. -/

/-- The globular identity at dimension 2:
    For a 2-cell f : p → q where p, q : M → N,
    we have src(src(f)) = src(tgt(f)) = M -/
theorem globular_src_2 (f : NConversion 2) :
    NConversion.source0 (NConversion.source1 f) =
    NConversion.source0 (NConversion.target1 f) := by
  exact NConversion.globular_src f

/-- The globular identity at dimension 2:
    For a 2-cell f : p → q where p, q : M → N,
    we have tgt(src(f)) = tgt(tgt(f)) = N -/
theorem globular_tgt_2 (f : NConversion 2) :
    NConversion.target0 (NConversion.source1 f) =
    NConversion.target0 (NConversion.target1 f) := by
  exact NConversion.globular_tgt f

/-- The globular identity at dimension 3 on source boundaries:
    for a 3-cell `η : α → β`, the 1-source of `α` equals the 1-source of `β`. -/
theorem globular_src_3 (f : NConversion 3) :
    NConversion.source (NConversion.source f) =
    NConversion.source (NConversion.target f) := by
  exact NConversion.globular_src f

/-- The globular identity at dimension 3 on target boundaries:
    for a 3-cell `η : α → β`, the 1-target of `α` equals the 1-target of `β`. -/
theorem globular_tgt_3 (f : NConversion 3) :
    NConversion.target (NConversion.source f) =
    NConversion.target (NConversion.target f) := by
  exact NConversion.globular_tgt f

/-- The higher-conversion tower seen as a generic globular tower. -/
abbrev LambdaTower := HigherLambdaModel.Simplicial.GlobularTower

/-- The canonical lambda tower with concrete λ-calculus types -/
def lambdaTower : LambdaTower where
  Cell := NConversion
  source := NConversion.source
  target := NConversion.target
  globular_src := NConversion.globular_src
  globular_tgt := NConversion.globular_tgt

/-! ## Summary

We have formalized Section 3 of the paper:

1. **N-Conversions (Σₙ)**: The tower of equivalences
   - Σ₀ = Terms
   - Σ₁ = βη-reduction sequences
   - Σ₂ = Homotopies between sequences
   - Σₙ (n ≥ 3) = Higher cells generated recursively from lower ones

2. **N-Terms (Πₙ)**: Computational witnesses
   - Π₀ = Terms
   - Π₁ = Redexes and sequences
   - Π₂ = Church-Rosser diamonds
   - Πₙ (n ≥ 3) = Explicit higher conversions

3. **Proposition 3.4**: Πₙ ⊆ Σₙ
   - Every n-term induces an n-conversion
   - This is given by `NTerm.toNConversion`

4. **Corollary**: TH_λ= ⊆ HoTFT
   - Classical βη-equality embeds into homotopic equality
   - This is `TH_lambda_eq_subset_HoTFT`

The key insight is that the higher structure of λ-calculus is not
an artificial construction but emerges naturally from the computational
content of β and η reduction.
-/

/-! ## Examples

Concrete demonstrations of the main results. -/

/-- The identity combinator I = λx.x -/
example : Term := Term.I

/-- The K combinator K = λx.λy.x (constant function) -/
example : Term := Term.K

/-- The S combinator S = λx.λy.λz.xz(yz) -/
example : Term := Term.S

/-- I M reduces to M via β in one step: (λx.x)M →β M -/
example (M : Term) : BetaStep (Term.I @ M) ((var 0)[M]) :=
  BetaStep.beta (var 0) M

/-- A term applied to itself: ω = λx.xx -/
def omega : Term := Term.lam (Term.app (Term.var 0) (Term.var 0))

/-- The famous Ω = ωω (the simplest divergent term) -/
def Omega : Term := Term.app omega omega

/-- Any term is βη-equivalent to itself (reflexivity) -/
example (M : Term) : M =_TH M := BetaEtaConv.refl M

/-- βη-equivalence is symmetric -/
example (M N : Term) (h : M =_TH N) : N =_TH M :=
  BetaEtaConv.symm' h

/-- βη-equivalence is transitive -/
example (M N P : Term) (h1 : M =_TH N) (h2 : N =_TH P) : M =_TH P :=
  BetaEtaConv.trans' h1 h2

/-- The main theorem in action: any βη-equivalent terms are equal in all
    extensional Kan complexes -/
example (M N : Term) (h : M =_TH N) : HoTFT_eq M N :=
  TH_lambda_eq_subset_HoTFT M N h

/-- β-reduction is sound: (λx.M)N =HoTFT M[N/x] -/
example (M N : Term) : HoTFT_eq (Term.app (Term.lam M) N) (M[N]) := by
  apply TH_lambda_eq_subset_HoTFT
  apply BetaEtaConv.of_closure
  apply BetaEtaClosure.single
  exact BetaEtaStep.beta (BetaStep.beta M N)

/-- The identity function applied to any term reduces to that term.
    This demonstrates how HoTFT captures computational behavior. -/
example (M : Term) : HoTFT_eq (Term.I @ M) ((var 0)[M]) := by
  apply TH_lambda_eq_subset_HoTFT
  apply BetaEtaConv.of_closure
  apply BetaEtaClosure.single
  exact BetaEtaStep.beta (BetaStep.beta (var 0) M)

/-! ### Church Boolean Examples -/

/-- Church true: λx.λy.x (same as K combinator) -/
example : Term.tru = Term.K := rfl

/-- Church false: λx.λy.y -/
example : Term.fls = Term.lam (Term.lam (Term.var 0)) := rfl

/-- tru x y →*β x: Church true selects its first argument

    tru = λa.λb.a, so (tru x) = (λb.x[a:=x]) after one β-step.
    The full reduction: (tru x y) →β ((λb.x') y) →β x'
    where x' is x with shifted indices. -/
example (x : Term) : BetaStep (Term.app Term.tru x) (Term.subst0 x (Term.lam (Term.var 1))) :=
  BetaStep.beta (Term.lam (Term.var 1)) x

/-! ### Church Numeral Examples -/

/-- Church zero: λf.λx.x (same as fls) -/
example : Term.zero = Term.fls := rfl

/-- Church one: λf.λx.fx -/
example : Term.one = Term.lam (Term.lam (Term.app (Term.var 1) (Term.var 0))) := rfl

/-- The successor function adds one application of f -/
example : Term.succ = Term.lam (Term.lam (Term.lam
    (Term.app (Term.var 1)
              (Term.app (Term.app (Term.var 2) (Term.var 1)) (Term.var 0))))) := rfl

/-! ### SKI Combinator Examples -/

/-- SKK computes the identity: SKK x →*β x

    Proof outline: S K K = (λxyz.xz(yz)) K K →* (λz.Kz(Kz)) →* λz.z

    This is a classic result showing that K and S are sufficient
    to express all computable functions. -/
example : BetaStep (Term.app Term.S Term.K)
    (Term.subst0 Term.K (Term.lam (Term.lam
      (Term.app (Term.app (Term.var 2) (Term.var 0)) (Term.app (Term.var 1) (Term.var 0)))))) :=
  BetaStep.beta _ _

/-! ### Combinator Definitions -/

/-- The B combinator (composition): λf.λg.λx.f(gx) -/
example : Term.B = Term.lam (Term.lam (Term.lam
    (Term.app (Term.var 2) (Term.app (Term.var 1) (Term.var 0))))) := rfl

/-- The C combinator (flip): λf.λx.λy.fyx -/
example : Term.C = Term.lam (Term.lam (Term.lam
    (Term.app (Term.app (Term.var 2) (Term.var 0)) (Term.var 1)))) := rfl

/-- The W combinator (duplicate): λf.λx.fxx -/
example : Term.W = Term.lam (Term.lam
    (Term.app (Term.app (Term.var 1) (Term.var 0)) (Term.var 0))) := rfl

/-! ### Fixed-Point Combinator Examples -/

/-- The Y combinator -/
example : Term.Y = Term.lam (Term.app
    (Term.lam (Term.app (Term.var 1) (Term.app (Term.var 0) (Term.var 0))))
    (Term.lam (Term.app (Term.var 1) (Term.app (Term.var 0) (Term.var 0))))) := rfl

/-- Turing's fixed-point combinator Θ -/
example : Term.Theta =
    let A := Term.lam (Term.lam (Term.app (Term.var 0)
                                 (Term.app (Term.app (Term.var 1) (Term.var 1)) (Term.var 0))))
    Term.app A A := rfl

/-! ### Church Pair Examples -/

/-- Church pair constructor -/
example : Term.pair = Term.lam (Term.lam (Term.lam
    (Term.app (Term.app (Term.var 0) (Term.var 2)) (Term.var 1)))) := rfl

/-- First projection uses tru (K combinator) -/
example : Term.fst = Term.lam (Term.app (Term.var 0) Term.tru) := rfl

/-- Second projection uses fls -/
example : Term.snd = Term.lam (Term.app (Term.var 0) Term.fls) := rfl

/-! ### Arithmetic Examples -/

/-- iszero returns tru for zero: iszero 0 →*βη tru -/
example : BetaStep (Term.iszero @ Term.zero)
    (Term.app (Term.app Term.zero (Term.lam Term.fls)) Term.tru) :=
  BetaStep.beta _ _

/-! ### η-Reduction Examples -/

/-- η-contraction: λx.Mx →η M when x ∉ FV(M)

    This is the extensionality principle for functions.
    The η rule says that if M doesn't use its argument (x ∉ FV(M)),
    then wrapping it in λx.Mx doesn't change its behavior.

    Example: λx.Kx →η K because x is not free in K.
    The target of the EtaStep is shift(-1,0,K) = K (since K is closed). -/
example (M : Term) (h : ¬Term.hasFreeVar 0 M = true) :
    EtaStep (Term.lam (Term.app M (Term.var 0))) (Term.shift (-1) 0 M) :=
  EtaStep.eta M h

/-- Concrete η-example: λx.Kx →η K -/
example : Term.isEtaRedex (Term.lam (Term.app Term.K (Term.var 0))) = true := rfl

/-! ### NTerm1 Indexed Type Examples -/

/-- A simple 1-term: single β-step from (λx.x)M to M -/
example (M : Term) : NTerm1 (Term.I @ M) ((var 0)[M]) :=
  NTerm1.redex (BetaEtaStep.beta (BetaStep.beta (var 0) M))

/-- Reflexivity: trivial path from M to M -/
example (M : Term) : NTerm1 M M :=
  NTerm1.refl

/-- Composition of 1-terms: if M →βη N and N →βη P, then M →βη P -/
example (M N P : Term) (h1 : BetaEtaStep M N) (h2 : BetaEtaStep N P) : NTerm1 M P :=
  NTerm1.seq (NTerm1.redex h1) (NTerm1.redex h2)

end HigherLambdaModel.Lambda.NTerms
