/-
# Coherence Laws for the Weak ω-Groupoid Structure on λ-Terms

This module establishes the coherence laws that make higher λ-terms form a weak ω-groupoid.
While `HigherTerms.lean` defines the basic groupoid operations (composition, inverses),
this module adds the **coherence conditions** that govern how these operations interact.

## Key Coherences

In a weak ω-groupoid, not all equalities hold strictly—instead, they hold "up to higher cells."
The main coherences are:

1. **Pentagon identity**: Two ways of reassociating ((p·q)·r)·s to p·(q·(r·s)) are equal
2. **Triangle identity**: Compatibility of associativity with unit laws
3. **Interchange law**: Horizontal and vertical composition of 2-cells commute
4. **Whiskering**: If α : p ≃ q, then we can compose with other paths
5. **Mac Lane coherence**: All diagrams of canonical isomorphisms commute

## The Role of 0-Truncation

Crucially, our formalization uses **0-truncation at dimension 2**: any two parallel 2-cells
are equal (via `Homotopy2.ofParallel`). This dramatically simplifies the coherence theory:

- All 3-cells are trivial (any two 2-cells are already equal)
- Pentagon, triangle, interchange become *automatic* (no witness needed)
- Only 2-cell constructions (whiskering) require explicit definitions

This reflects the extensional nature of λ-models: in an extensional Kan complex,
the hom-spaces are contractible, collapsing all higher structure.

## References

- Martínez-Rivillas & de Queiroz, "The Theory of an Arbitrary Higher λ-Model"
- Mac Lane, "Categories for the Working Mathematician" (Chapter VII: Coherence)
- Lumsdaine, "Weak ω-categories from intensional type theory"
-/

import HigherLambdaModel.Lambda.HigherTerms

namespace HigherLambdaModel.Lambda.Coherence

open Term
open HigherLambdaModel.Lambda.HigherTerms

/-! ## Whiskering Operations

Whiskering allows us to compose 2-cells with 1-cells. If α : p ≃ q is a homotopy,
we can "whisker" it on the left or right by composing with another path.

These are the horizontal compositions in the bicategorical structure. -/

/-- **Left whiskering**: Compose a 2-cell on the right with a path on the left.
    If α : p ≃ q, then r · α : (r · p) ≃ (r · q).

    This witnesses that concatenation respects homotopy in its second argument. -/
def whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (_ : Homotopy2 p q) :
    Homotopy2 (ReductionSeq.concat r p) (ReductionSeq.concat r q) :=
  Homotopy2.ofParallel _ _

/-- **Right whiskering**: Compose a 2-cell on the left with a path on the right.
    If α : p ≃ q, then α · s : (p · s) ≃ (q · s).

    This witnesses that concatenation respects homotopy in its first argument. -/
def whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (_ : Homotopy2 p q)
    (s : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p s) (ReductionSeq.concat q s) :=
  Homotopy2.ofParallel _ _

/-- **Horizontal composition**: Compose two 2-cells horizontally.
    If α : p ≃ p' and β : q ≃ q', then α ⋆ β : (p·q) ≃ (p'·q').

    This is the composition operation at the 2-cell level. It can be defined
    in two equivalent ways (interchange law):
    - (α · q') ∘ (p · β)
    - (p' · β) ∘ (α · q)

    With 0-truncation, these are automatically equal. -/
def hcomp {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (_ : Homotopy2 p p') (_ : Homotopy2 q q') :
    Homotopy2 (ReductionSeq.concat p q) (ReductionSeq.concat p' q') :=
  Homotopy2.ofParallel _ _

/-! ## Whiskering Properties

The whiskering operations satisfy various properties that make them well-behaved
functorial operations. -/

/-- Left whiskering preserves identity 2-cells. -/
theorem whiskerLeft_refl {M N P : Term}
    (r : ReductionSeq M N) (p : ReductionSeq N P) :
    whiskerLeft r (Homotopy2.refl p) = Homotopy2.refl (ReductionSeq.concat r p) := by
  unfold whiskerLeft
  rfl

/-- Right whiskering preserves identity 2-cells. -/
theorem whiskerRight_refl {M N P : Term}
    (p : ReductionSeq M N) (s : ReductionSeq N P) :
    whiskerRight (Homotopy2.refl p) s = Homotopy2.refl (ReductionSeq.concat p s) := by
  unfold whiskerRight
  rfl

/-- Left whiskering preserves composition of 2-cells. -/
theorem whiskerLeft_trans {M N P : Term}
    (r : ReductionSeq M N) {p q s : ReductionSeq N P}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    whiskerLeft r (Homotopy2.trans α β) =
    Homotopy2.trans (whiskerLeft r α) (whiskerLeft r β) := by
  cases α
  cases β
  unfold whiskerLeft Homotopy2.trans
  rfl

/-- Right whiskering preserves composition of 2-cells. -/
theorem whiskerRight_trans {M N P : Term}
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s)
    (r : ReductionSeq N P) :
    whiskerRight (Homotopy2.trans α β) r =
    Homotopy2.trans (whiskerRight α r) (whiskerRight β r) := by
  cases α
  cases β
  unfold whiskerRight Homotopy2.trans
  rfl

/-- Left whiskering preserves symmetry. -/
theorem whiskerLeft_symm {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    whiskerLeft r (Homotopy2.symm α) =
    Homotopy2.symm (whiskerLeft r α) := by
  cases α
  unfold whiskerLeft Homotopy2.symm
  rfl

/-- Right whiskering preserves symmetry. -/
theorem whiskerRight_symm {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    whiskerRight (Homotopy2.symm α) s =
    Homotopy2.symm (whiskerRight α s) := by
  cases α
  unfold whiskerRight Homotopy2.symm
  rfl

/-! ## Interchange Law

The interchange law states that the two ways of composing 2-cells commute:
vertical composition interchanges with horizontal composition.

Given:
```
  M --p-→ N --q-→ P
  |  α   |  β   |
  M --p'-→ N --q'-→ P
  |  α'  |  β'  |
  M --p''-→ N --q''-→ P
```

We can compose either:
1. Vertically first: (α ∘ α') ⋆ (β ∘ β')
2. Horizontally first: (α ⋆ β) ∘ (α' ⋆ β')

The interchange law says these are equal.

With 0-truncation, this is automatic: both compositions yield a 2-cell
between p·q and p''·q'', and all such 2-cells are equal. -/

/-- **Interchange law**: Vertical and horizontal composition of 2-cells commute.

    This is one of the fundamental coherences in bicategory theory. In our
    0-truncated setting, it holds trivially because all parallel 2-cells are equal. -/
theorem interchange {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    hcomp α β = Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β) := by
  cases α
  cases β
  unfold hcomp whiskerRight whiskerLeft Homotopy2.trans
  rfl

/-- Alternative form of interchange using the other parenthesization. -/
theorem interchange' {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    hcomp α β = Homotopy2.trans (whiskerLeft p β) (whiskerRight α q') := by
  cases α
  cases β
  unfold hcomp whiskerLeft whiskerRight Homotopy2.trans
  rfl

/-! ## Associativity Coherence (Pentagon)

The pentagon identity governs associativity of composition. Given four paths
p, q, r, s, there are two ways to reassociate ((p·q)·r)·s to p·(q·(r·s)):

1. Via ((p·q)·r)·s ≃ (p·q)·(r·s) ≃ p·(q·(r·s))
2. Via ((p·q)·r)·s ≃ (p·(q·r))·s ≃ p·((q·r)·s) ≃ p·(q·(r·s))

The pentagon law states these two 2-cells are equal (as 3-cells).

However, in our formalization, associativity holds **definitionally**
(see `ReductionSeq.concat_assoc`), so the associator is the identity 2-cell. -/

/-- The associator 2-cell witnessing that concatenation is associative.
    Since associativity holds definitionally, this is simply `refl`. -/
def associator {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.concat p q) r)
              (ReductionSeq.concat p (ReductionSeq.concat q r)) := by
  rw [ReductionSeq.concat_assoc]
  exact Homotopy2.refl _

/-- **Pentagon coherence**: The two ways of reassociating four paths are equal.

    Since associativity holds definitionally, all associators are `refl`,
    and the pentagon law becomes the equation refl = refl, which is automatic.

    In a non-definitional setting, this would be a non-trivial 3-cell. -/
theorem pentagon {M N P Q R : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P)
    (r : ReductionSeq P Q) (s : ReductionSeq Q R) :
    Homotopy2.trans (associator (ReductionSeq.concat p q) r s)
                    (associator p q (ReductionSeq.concat r s)) =
    Homotopy2.trans (Homotopy2.trans (whiskerRight (associator p q r) s)
                                      (associator p (ReductionSeq.concat q r) s))
                    (whiskerLeft p (associator q r s)) := by
  unfold associator whiskerRight whiskerLeft Homotopy2.trans
  rfl

/-! ## Unit Coherence (Triangle)

The triangle identity governs the interaction between associativity and unit laws.
Given paths p, q, there are two ways to go from (p · refl) · q to p · q:

1. Via associativity: (p · refl) · q ≃ p · (refl · q) ≃ p · q
2. Via unit laws directly: (p · refl) · q ≃ p · q

The triangle law states these are equal.

Since both concat_refl_left and concat_refl_right hold definitionally,
the unitors are also reflexivity 2-cells. -/

/-- The left unitor: witnesses that refl is a left identity for concatenation.
    Since left identity holds definitionally, this is `refl`. -/
def leftUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.refl M) p) p :=
  Homotopy2.refl _

/-- The right unitor: witnesses that refl is a right identity for concatenation.
    Since right identity holds definitionally (by `concat_refl_right`),
    this is `refl`. -/
def rightUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat p (ReductionSeq.refl N)) p := by
  rw [ReductionSeq.concat_refl_right]
  exact Homotopy2.refl _

/-- **Triangle coherence**: Compatibility of associator with unitors.

    This states that the two ways of simplifying (p · refl) · q are equal:
    - Via associator then left unitor: (p·refl)·q ≃ p·(refl·q) ≃ p·q
    - Via right unitor on p: (p·refl)·q ≃ p·q

    With definitional unit laws, all unitors are refl, making this automatic. -/
theorem triangle {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) :
    Homotopy2.trans (associator p (ReductionSeq.refl N) q)
                    (whiskerLeft p (leftUnitor q)) =
    whiskerRight (rightUnitor p) q := by
  unfold associator leftUnitor rightUnitor whiskerLeft whiskerRight Homotopy2.trans
  rfl

/-! ## Mac Lane Coherence Theorem

Mac Lane's coherence theorem for monoidal categories states that "all diagrams
of canonical isomorphisms commute." For groupoids, this means all canonical
2-cells (built from associators, unitors, and their inverses) between parallel
paths are equal.

In our 0-truncated setting, this is automatic: **any** two parallel 2-cells
are equal, not just the canonical ones. -/

/-- **Mac Lane coherence**: All canonical 2-cells between parallel paths are equal.

    A "canonical" 2-cell is one built from:
    - Reflexivity
    - Associators and unitors
    - Composition and inverses of the above

    In our 0-truncated formalization, this follows immediately: all 2-cells
    between any parallel paths are equal, whether canonical or not. -/
theorem macLane_coherence {M N : Term}
    (p q : ReductionSeq M N)
    (α β : Homotopy2 p q) :
    α = β := by
  cases α
  cases β
  rfl

/-! ## Coherence for Inverses

The inverse operation also requires coherence laws. These state that
the inverse is well-behaved with respect to composition and units. -/

/-- Inverse of refl is homotopic to refl.
    Since inv is axiomatized, we can only assert this holds up to homotopy. -/
def inv_refl_homotopy {M : Term} :
    Homotopy2 (ReductionSeq.refl M).inv (ReductionSeq.refl M) :=
  Homotopy2.ofParallel _ _

/-- Inverse distributes over composition (as an anti-homomorphism). -/
def inv_concat {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p q).inv
              (ReductionSeq.concat q.inv p.inv) :=
  Homotopy2.ofParallel _ _

/-- Double inverse returns to the original path. -/
def inv_inv {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 p.inv.inv p :=
  Homotopy2.ofParallel _ _

/-- Inverse of left-whisker equals left-whisker of inverse. -/
theorem inv_whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    Homotopy2.symm (whiskerLeft r α) = whiskerLeft r (Homotopy2.symm α) := by
  cases α
  unfold whiskerLeft Homotopy2.symm
  rfl

/-- Inverse of right-whisker equals right-whisker of inverse. -/
theorem inv_whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    Homotopy2.symm (whiskerRight α s) = whiskerRight (Homotopy2.symm α) s := by
  cases α
  unfold whiskerRight Homotopy2.symm
  rfl

/-! ## Higher Coherences

In a full weak ω-groupoid, there are coherences at all dimensions:
- 3-cells: coherence for pentagon, triangle, etc.
- 4-cells: coherence for 3-cell coherences
- And so on...

However, with 0-truncation at dimension 2, **all higher coherences are automatic**:
- All 3-cells are trivial (any two parallel 2-cells are equal by `macLane_coherence`)
- All 4-cells and higher are trivially trivial (no non-trivial 3-cells to compare)

This dramatically simplifies the theory: we only need to define 2-cell operations
(whiskering), and all coherence laws become trivial equalities. -/

/-- The type of 3-cells: homotopies between 2-cells.
    With 0-truncation, this is always `Unit` (all 2-cells are equal). -/
def Homotopy3 {M N : Term} {p q : ReductionSeq M N}
    (_ _ : Homotopy2 p q) : Type :=
  Unit

/-- Any two parallel 2-cells are connected by a (trivial) 3-cell.
    This is the 1-truncation property at dimension 3. -/
def Homotopy3.mk {M N : Term} {p q : ReductionSeq M N}
    (α β : Homotopy2 p q) : Homotopy3 α β :=
  ()

/-- All 3-cells are equal (0-truncation at dimension 3).
    This makes all higher coherence laws automatic. -/
theorem Homotopy3.eq {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (γ δ : Homotopy3 α β) :
    γ = δ :=
  rfl

/-! ## Coherence Structure Summary

We've established the coherence structure for the weak ω-groupoid of λ-terms:

**2-cell operations** (explicitly defined):
- `whiskerLeft`: Compose 2-cells with paths on the left
- `whiskerRight`: Compose 2-cells with paths on the right
- `hcomp`: Horizontal composition of 2-cells

**Coherence laws** (automatic via 0-truncation):
- Pentagon identity: Associativity coherence for four paths
- Triangle identity: Compatibility of associativity and units
- Interchange law: Vertical/horizontal composition commute
- Mac Lane coherence: All canonical 2-cells are equal
- Inverse coherences: Inverse interacts well with operations

**Higher coherences** (trivially automatic):
- All 3-cells are trivial (any two 2-cells are equal)
- All 4-cells and higher are trivially trivial

**Why this works**:
The 0-truncation property (`Homotopy2.ofParallel`) encodes that in an
**extensional Kan complex** (homotopic λ-model), the hom-spaces between any
two terms are contractible. This collapses all higher structure:

1. Any two reduction sequences M →* N are homotopic (connected by a 2-cell)
2. Any two such homotopies are equal (no non-trivial 3-cells)
3. Therefore all coherence laws hold automatically

This is the key simplification that makes higher λ-theory tractable:
the extensional/Kan assumption eliminates most of the coherence complexity. -/

/-! ## The Weak ω-Groupoid Structure

We can now package all the coherence data into a proper weak ω-groupoid structure. -/

/-- The weak ω-groupoid structure on λ-terms, with all coherence laws. -/
structure LambdaOmegaGroupoid where
  /-- Associativity (holds definitionally) -/
  comp_assoc : {M N P Q : Term} → (p : ReductionSeq M N) → (q : ReductionSeq N P) →
    (r : ReductionSeq P Q) →
    (p.concat q).concat r = p.concat (q.concat r) := ReductionSeq.concat_assoc
  /-- Left identity (holds definitionally) -/
  comp_id_left : {M N : Term} → (p : ReductionSeq M N) →
    (ReductionSeq.refl M).concat p = p := ReductionSeq.concat_refl_left
  /-- Right identity (requires proof) -/
  comp_id_right : {M N : Term} → (p : ReductionSeq M N) →
    p.concat (ReductionSeq.refl N) = p := ReductionSeq.concat_refl_right
  /-- 0-truncation: any two parallel 2-cells are equal -/
  hom2_unique : {M N : Term} → {p q : ReductionSeq M N} → (α β : Homotopy2 p q) → α = β :=
    fun {_} {_} {p} {q} α β => macLane_coherence p q α β
  /-- Pentagon coherence (automatic) -/
  pentagon_coh : {M N P Q R : Term} → (p : ReductionSeq M N) → (q : ReductionSeq N P) →
    (r : ReductionSeq P Q) → (s : ReductionSeq Q R) →
    Homotopy2.trans (associator (p.concat q) r s) (associator p q (r.concat s)) =
    Homotopy2.trans (Homotopy2.trans (whiskerRight (associator p q r) s)
                                      (associator p (q.concat r) s))
                    (whiskerLeft p (associator q r s)) := pentagon
  /-- Triangle coherence (automatic) -/
  triangle_coh : {M N P : Term} → (p : ReductionSeq M N) → (q : ReductionSeq N P) →
    Homotopy2.trans (associator p (ReductionSeq.refl N) q) (whiskerLeft p (leftUnitor q)) =
    whiskerRight (rightUnitor p) q := triangle
  /-- Interchange law (automatic) -/
  interchange_coh : {M N P : Term} → {p p' : ReductionSeq M N} → {q q' : ReductionSeq N P} →
    (α : Homotopy2 p p') → (β : Homotopy2 q q') →
    hcomp α β = Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β) := interchange

/-- The canonical weak ω-groupoid structure on λ-terms. -/
def lambdaOmegaGroupoid : LambdaOmegaGroupoid := {
  comp_assoc := ReductionSeq.concat_assoc
  comp_id_left := ReductionSeq.concat_refl_left
  comp_id_right := ReductionSeq.concat_refl_right
  hom2_unique := fun {_} {_} {p} {q} α β => macLane_coherence p q α β
  pentagon_coh := pentagon
  triangle_coh := triangle
  interchange_coh := interchange
}

/-! ## Connection to Homotopy Theory

The coherence structure we've defined makes precise the sense in which
"higher βη-conversions form a weak ω-groupoid" (the paper's main result).

**Homotopy interpretation**:
- 0-cells (terms) are "spaces" or "types"
- 1-cells (reduction sequences) are "paths" or "identity proofs"
- 2-cells (homotopies) are "path homotopies" or "proofs of path equality"
- 3-cells and higher collapse due to extensionality

**Key properties**:
1. Every term is connected to itself by the identity path (refl)
2. Paths compose associatively (up to 2-cell)
3. Every path has an inverse (up to 2-cell)
4. All coherence diagrams commute (automatically via 0-truncation)

**Why this matters for λ-calculus**:
The paper shows that in any **homotopic λ-model** (extensional Kan complex),
the type of λ-terms automatically carries this structure. Our formalization
proves that all the expected coherence laws hold, making the higher structure
well-behaved and predictable.

This is the foundation for:
- **Higher λ-theory**: Extending λ-calculus with higher identity types
- **Homotopic models**: Models where equality has computational content
- **Coherence theorems**: All ways of proving equality are "the same"
-/

end HigherLambdaModel.Lambda.Coherence
