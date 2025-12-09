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
- Σₙ₊₁ = equivalences between n-conversions -/

/-- The type of n-conversions.

    Σ₀ = Term (λ-terms)
    Σ₁ = pairs of terms with a reduction sequence (1-conversions)
    Σ₂ = homotopies between parallel reduction sequences (2-conversions)
    Σₙ for n ≥ 3 = trivial (in extensional models, 1-truncation)

    Note: In a fully extensional model, 2-cells and above are all connected. -/
def NConversion : Nat → Type
  | 0 => Term
  | 1 => Σ (M N : Term), ReductionSeq M N
  | 2 => Σ (M N : Term) (p q : ReductionSeq M N), Homotopy2 p q
  | _ + 3 => Unit  -- Higher conversions are trivial in extensional models

/-- The source of an n-conversion (for n ≥ 1).
    For n ≥ 2, this is partial since all higher cells are contractible. -/
def NConversion.source0 : NConversion 1 → NConversion 0
  | ⟨M, _, _⟩ => M

def NConversion.source1 : NConversion 2 → NConversion 1
  | ⟨M, N, p, _, _⟩ => ⟨M, N, p⟩

/-- The target of an n-conversion -/
def NConversion.target0 : NConversion 1 → NConversion 0
  | ⟨_, N, _⟩ => N

def NConversion.target1 : NConversion 2 → NConversion 1
  | ⟨M, N, _, q, _⟩ => ⟨M, N, q⟩

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
    For n ≥ 3: Trivial in extensional models -/
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
  /-- Higher terms are trivial -/
  | trivial : (n : Nat) → NTerm (n + 3)

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

/-- Well-formedness is now a theorem, not an axiom!
    For the seq smart constructor, endpoints must match by construction. -/
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
    ⟨M, P, ReductionSeq.concat p₁ q₁, ReductionSeq.concat p₂ q₂, Homotopy2.ofParallel _ _⟩
  | 2, NTerm.refl2 p => ⟨_, _, p, p, Homotopy2.refl p⟩
  | _ + 3, _ => ()  -- Higher conversions are trivial

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
    interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | beta M N =>
    -- Root β-redex: (λM)N →β M[N]
    exact beta_sound K M N ρ
  | appL hstep ih =>
    -- β-reduction in function position: app M N → app M' N
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | appR hstep ih =>
    -- β-reduction in argument position: app M N → app M N'
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | lam hstep ih =>
    -- β-reduction under λ: lam M → lam M'
    simp only [interpret]
    congr 1
    funext f
    exact ih (fun n => if n = 0 then f else ρ (n - 1))

/-- Soundness of a single η-step in an extensional Kan complex.
    This proves that η-reduction preserves interpretation. -/
theorem etaStep_sound (K : ExtensionalKanComplex) (M N : Term)
    (h : EtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | eta M hfv =>
    -- Root η-redex: λx.Mx →η M when x ∉ FV(M)
    -- The source is (lam (app M (var 0))) where hasFreeVar 0 M = false
    -- The target is (shift (-1) 0 M)
    -- We need: interpret ρ (lam (app M (var 0))) = interpret ρ (shift (-1) 0 M)

    -- First, extract the hypothesis that M doesn't have variable 0 free
    have h_not_free : Term.hasFreeVar 0 M = false := by
      simp at hfv
      exact hfv

    -- Expand the interpretation of (lam (app M (var 0)))
    simp only [interpret, ReflexiveKanComplex.app]

    -- We have: G(λf. F(⟦M⟧ρ')(f)) where ρ' = (fun n => if n = 0 then f else ρ (n - 1))
    -- We want to show this equals: ⟦shift (-1) 0 M⟧ρ

    -- Step 1: Use interpret_unshift to relate ⟦M⟧ρ' to ⟦shift (-1) 0 M⟧ρ
    have key : ∀ f, interpret K.toReflexiveKanComplex
                      (fun n => if n = 0 then f else ρ (n - 1)) M =
                   interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M) := by
      intro f
      exact interpret_unshift K.toReflexiveKanComplex M ρ f h_not_free

    -- The goal is: K.G (λf. K.F (⟦M⟧ρ') f) = ⟦shift (-1) 0 M⟧ρ
    -- After using key, we get: K.G (λf. K.F (⟦shift (-1) 0 M⟧ρ) f) = ⟦shift (-1) 0 M⟧ρ
    -- By function extensionality: (λf. K.F x f) = K.F x
    -- So we need: K.G (K.F (⟦shift (-1) 0 M⟧ρ)) = ⟦shift (-1) 0 M⟧ρ
    -- This is exactly epsilon (in reverse)

    -- Step 2: Show the inner functions are equal
    -- Note: simp normalizes 0 = 0 to True, so we use True in the statement
    have inner_eq : (fun f => K.F (interpret K.toReflexiveKanComplex
                                     (fun n => if n = 0 then f else ρ (n - 1)) M)
                                   (if True then f else ρ (0 - 1))) =
                    K.F (interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M)) := by
      funext f
      simp only [ite_true, key]

    rw [inner_eq]
    -- Now goal is: K.G (K.F (⟦shift (-1) 0 M⟧ρ)) = ⟦shift (-1) 0 M⟧ρ
    exact (K.epsilon (interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M))).symm

  | appL hstep ih =>
    -- η-reduction in function position
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | appR hstep ih =>
    -- η-reduction in argument position
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | lam hstep ih =>
    -- η-reduction under λ
    simp only [interpret]
    congr 1
    funext f
    exact ih (fun n => if n = 0 then f else ρ (n - 1))

/-- Soundness of a single βη-step in an extensional Kan complex.

    This is a fundamental soundness theorem for the interpretation of λ-terms
    in extensional Kan complexes. The proof works by case analysis on whether
    the step is a β-step or η-step, and then uses the corresponding soundness theorem. -/
theorem betaEtaStep_sound (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaEtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  cases h with
  | beta hb => exact betaStep_sound K M N hb ρ
  | eta he => exact etaStep_sound K M N he ρ

/-- Soundness for the indexed NTerm1 type -/
theorem nterm1_indexed_sound (K : ExtensionalKanComplex) {M N : Term} (t : NTerm1 M N)
    (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction t with
  | redex h =>
    exact betaEtaStep_sound K _ _ h ρ
  | seq t₁ t₂ ih₁ ih₂ =>
    exact ih₁.trans ih₂
  | refl =>
    rfl

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
  intro K
  intro ρ
  -- The proof goes by induction on the βη-conversion
  induction h with
  | refl _ => rfl
  | step s _ ih =>
    -- Single step: need to show ⟦M⟧ = ⟦M'⟧ when M →βη M'
    have h1 := betaEtaStep_sound K _ _ s ρ
    exact h1.trans ih
  | stepInv s _ ih =>
    -- Reverse step: use symmetry
    have h1 := betaEtaStep_sound K _ _ s ρ
    exact h1.symm.trans ih

/-! ## The Full Tower: Weak ω-Groupoid Structure

The paper shows that the tower (Σ₀, Σ₁, Σ₂, ...) forms a weak ω-groupoid.
We characterize the low-dimensional structure explicitly. -/

/-- The globular identity at dimension 2:
    For a 2-cell f : p → q where p, q : M → N,
    we have src(src(f)) = src(tgt(f)) = M -/
theorem globular_src_2 (f : NConversion 2) :
    NConversion.source0 (NConversion.source1 f) =
    NConversion.source0 (NConversion.target1 f) := by
  obtain ⟨M, _, _, _, _⟩ := f
  rfl

/-- The globular identity at dimension 2:
    For a 2-cell f : p → q where p, q : M → N,
    we have tgt(src(f)) = tgt(tgt(f)) = N -/
theorem globular_tgt_2 (f : NConversion 2) :
    NConversion.target0 (NConversion.source1 f) =
    NConversion.target0 (NConversion.target1 f) := by
  obtain ⟨_, N, _, _, _⟩ := f
  rfl

/-- The tower of n-conversions packaged as data.
    This captures the essential ω-groupoid structure. -/
structure LambdaTower where
  /-- 0-cells: λ-terms -/
  Cell0 : Type
  /-- 1-cells: paths between 0-cells -/
  Cell1 : Cell0 → Cell0 → Type
  /-- 2-cells: homotopies between parallel 1-cells -/
  Cell2 : {M N : Cell0} → Cell1 M N → Cell1 M N → Type
  /-- 3-cells and above: trivial (contractible) -/
  CellHigher : (n : Nat) → (n ≥ 3) → Type

/-- The canonical lambda tower with concrete λ-calculus types -/
def lambdaTower : LambdaTower where
  Cell0 := Term
  Cell1 := ReductionSeq
  Cell2 := Homotopy2
  CellHigher := fun _ _ => Unit

/-! ## Summary

We have formalized Section 3 of the paper:

1. **N-Conversions (Σₙ)**: The tower of equivalences
   - Σ₀ = Terms
   - Σ₁ = βη-reduction sequences
   - Σ₂ = Homotopies between sequences
   - Σₙ (n ≥ 3) = Trivial in extensional models

2. **N-Terms (Πₙ)**: Computational witnesses
   - Π₀ = Terms
   - Π₁ = Redexes and sequences
   - Π₂ = Church-Rosser diamonds
   - Πₙ (n ≥ 3) = Trivial

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
