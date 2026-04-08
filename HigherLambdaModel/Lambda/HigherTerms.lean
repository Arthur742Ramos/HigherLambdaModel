/-
# Higher λ-Terms

This module provides a fully constructive core for the higher-structure layer of the
repository.

The key design choice is that 1-cells are represented by **explicit βη
conversion zigzags**, not only by forward reduction sequences. This matters
because the paper's higher structure is groupoidal, so 1-cells need a
constructive inverse operation. With a purely directed reduction-sequence
encoding, such an inverse cannot be defined in general.

The current encoding therefore uses:

- `ReductionSeq M N` for explicit βη conversion paths from `M` to `N`
- `Homotopy2 p q` for proof-relevant 2-cell derivations between explicit paths
- `Homotopy3 α β` for proof-relevant 3-cell derivations between explicit 2-cells

This keeps the higher layer constructive while preserving the repository's main
soundness theorems, without collapsing low-dimensional higher cells to proof
irrelevant wrappers.
-/

import HigherLambdaModel.Lambda.Reduction
import HigherLambdaModel.Simplicial.OmegaGroupoid

namespace HigherLambdaModel.Lambda.HigherTerms

open Term

/-! ## Explicit βη Conversion Paths -/

/-- An explicit βη conversion path from `M` to `N`.

This is a type-valued presentation of `BetaEtaConv`: each constructor records
one forward or backward βη step, so inverses can be defined by path reversal. -/
inductive ReductionSeq : Term → Term → Type where
  | refl (M : Term) : ReductionSeq M M
  | step {M N P : Term} : BetaEtaStep M N → ReductionSeq N P → ReductionSeq M P
  | stepInv {M N P : Term} : BetaEtaStep N M → ReductionSeq N P → ReductionSeq M P

namespace ReductionSeq

/-- The number of generating βη steps in the path. -/
def length : {M N : Term} → ReductionSeq M N → Nat
  | _, _, refl _ => 0
  | _, _, step _ rest => rest.length + 1
  | _, _, stepInv _ rest => rest.length + 1

/-- Concatenation of explicit conversion paths. -/
def concat {M N P : Term} : ReductionSeq M N → ReductionSeq N P → ReductionSeq M P
  | refl _, q => q
  | step s rest, q => step s (concat rest q)
  | stepInv s rest, q => stepInv s (concat rest q)

/-- Concatenation is associative. -/
theorem concat_assoc {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    concat (concat p q) r = concat p (concat q r) := by
  induction p with
  | refl _ => rfl
  | step _ rest ih =>
    simp only [concat]
    rw [ih]
  | stepInv _ rest ih =>
    simp only [concat]
    rw [ih]

/-- Left identity for concatenation. -/
theorem concat_refl_left {M N : Term} (p : ReductionSeq M N) :
    concat (refl M) p = p := by
  -- Case-split to show concat(refl, p) computes to p in each branch.
  cases p with
  | refl M =>
      change refl M = refl M
      rfl
  | step s rest =>
      change step s rest = step s rest
      rfl
  | stepInv s rest =>
      change stepInv s rest = stepInv s rest
      rfl

/-- Right identity for concatenation. -/
theorem concat_refl_right {M N : Term} (p : ReductionSeq M N) :
    concat p (refl N) = p := by
  induction p with
  | refl _ => rfl
  | step _ rest ih =>
    simp only [concat]
    rw [ih]
  | stepInv _ rest ih =>
    simp only [concat]
    rw [ih]

/-- Interpret an explicit path as a proposition-level βη conversion. -/
def toBetaEtaConv : {M N : Term} → ReductionSeq M N → BetaEtaConv M N
  | _, _, refl M => BetaEtaConv.refl M
  | _, _, step s rest => BetaEtaConv.step s rest.toBetaEtaConv
  | _, _, stepInv s rest => BetaEtaConv.stepInv s rest.toBetaEtaConv

/-- A single forward βη step as an explicit path. -/
def single {M N : Term} (s : BetaEtaStep M N) : ReductionSeq M N :=
  step s (refl N)

/-- A single backward βη step as an explicit path. -/
def singleInv {M N : Term} (s : BetaEtaStep N M) : ReductionSeq M N :=
  stepInv s (refl N)

/-- Reversal of an explicit βη conversion path. -/
def inv : {M N : Term} → ReductionSeq M N → ReductionSeq N M
  | _, _, refl M => refl M
  | _, _, step s rest => concat rest.inv (singleInv s)
  | _, _, stepInv s rest => concat rest.inv (single s)

/-- Reversal of concatenation. -/
theorem inv_concat {M N P : Term} (p : ReductionSeq M N) (q : ReductionSeq N P) :
    (concat p q).inv = concat q.inv p.inv := by
  induction p with
  | refl _ =>
    exact (concat_refl_right q.inv).symm
  | step s rest ih =>
    simp only [concat, inv, ih]
    rw [concat_assoc]
  | stepInv s rest ih =>
    simp only [concat, inv, ih]
    rw [concat_assoc]

/-- Reversing twice returns the original path. -/
theorem inv_inv {M N : Term} (p : ReductionSeq M N) : p.inv.inv = p := by
  induction p with
  | refl _ => rfl
  | step s rest ih =>
    simp [inv, inv_concat, ih, single, singleInv, concat]
  | stepInv s rest ih =>
    simp [inv, inv_concat, ih, single, singleInv, concat]

/-- Every proposition-level βη conversion can be represented by an explicit path. -/
theorem exists_path_of_betaEtaConv {M N : Term} (h : BetaEtaConv M N) :
    ∃ p : ReductionSeq M N, p.toBetaEtaConv = h := by
  induction h with
  | refl M =>
    exact ⟨refl M, rfl⟩
  | step s rest ih =>
    rcases ih with ⟨p, rfl⟩
    exact ⟨step s p, rfl⟩
  | stepInv s rest ih =>
    rcases ih with ⟨p, rfl⟩
    exact ⟨stepInv s p, rfl⟩

/-- A chosen explicit path representative of a proposition-level βη-conversion.
This uses `Classical.choice` only on the fully proved existence theorem above. -/
noncomputable def ofBetaEtaConv {M N : Term} (h : BetaEtaConv M N) : ReductionSeq M N := by
  classical
  exact Classical.choose (exists_path_of_betaEtaConv h)

/-- Forgetting the chosen explicit path recovers the original conversion proof. -/
theorem toBetaEtaConv_ofBetaEtaConv {M N : Term} (h : BetaEtaConv M N) :
    (ofBetaEtaConv h).toBetaEtaConv = h := by
  classical
  exact Classical.choose_spec (exists_path_of_betaEtaConv h)

end ReductionSeq

/-! ## 2-Cells and 3-Cells -/

/-- Two paths are parallel when they have the same source and target. -/
def Parallel {M N P Q : Term} (_p : ReductionSeq M N) (_q : ReductionSeq P Q) : Prop :=
  M = P ∧ N = Q

/-- A proof-relevant derivation witnessing how a 2-cell between explicit paths
was constructed.

This records whether the 2-cell arose from a basic confluence diamond, from
reflexivity, or by composing/whiskering previously constructed 2-cells. -/
inductive Homotopy2Deriv : {M N : Term} → ReductionSeq M N → ReductionSeq M N → Type where
  | refl {M N : Term} (p : ReductionSeq M N) : Homotopy2Deriv p p
  | ofEq {M N : Term} {p q : ReductionSeq M N} :
      p = q → Homotopy2Deriv p q
  | symm {M N : Term} {p q : ReductionSeq M N} :
      Homotopy2Deriv p q → Homotopy2Deriv q p
  | trans {M N : Term} {p q r : ReductionSeq M N} :
      Homotopy2Deriv p q → Homotopy2Deriv q r → Homotopy2Deriv p r
  | diamond {M N₁ N₂ P : Term}
      (p₁ : ReductionSeq M N₁) (p₂ : ReductionSeq M N₂)
      (q₁ : ReductionSeq N₁ P) (q₂ : ReductionSeq N₂ P) :
      Homotopy2Deriv (ReductionSeq.concat p₁ q₁) (ReductionSeq.concat p₂ q₂)
  | whiskerLeft {M N P : Term} (r : ReductionSeq M N)
      {p q : ReductionSeq N P} :
      Homotopy2Deriv p q →
      Homotopy2Deriv (ReductionSeq.concat r p) (ReductionSeq.concat r q)
  | whiskerRight {M N P : Term} {p q : ReductionSeq M N} :
      Homotopy2Deriv p q → (s : ReductionSeq N P) →
      Homotopy2Deriv (ReductionSeq.concat p s) (ReductionSeq.concat q s)

/-- A 2-cell between parallel paths is a proof-relevant derivation witnessing
how one explicit path is related to the other. -/
structure Homotopy2 {M N : Term} (p q : ReductionSeq M N) where
  deriv : Homotopy2Deriv p q

namespace Homotopy2

/-- Reflexivity of 2-cells. -/
def refl {M N : Term} (p : ReductionSeq M N) : Homotopy2 p p :=
  { deriv := Homotopy2Deriv.refl p }

/-- A 2-cell induced by literal equality of paths. -/
def ofEq {M N : Term} {p q : ReductionSeq M N} (h : p = q) : Homotopy2 p q := by
  cases h
  exact { deriv := Homotopy2Deriv.ofEq rfl }

/-- A 2-cell induced by an explicit confluence diamond. -/
def ofDiamond {M N₁ N₂ P : Term}
    (p₁ : ReductionSeq M N₁) (p₂ : ReductionSeq M N₂)
    (q₁ : ReductionSeq N₁ P) (q₂ : ReductionSeq N₂ P) :
    Homotopy2 (ReductionSeq.concat p₁ q₁) (ReductionSeq.concat p₂ q₂) :=
  { deriv := Homotopy2Deriv.diamond p₁ p₂ q₁ q₂ }

/-- Symmetry of 2-cells. -/
def symm {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) : Homotopy2 q p :=
  { deriv := Homotopy2Deriv.symm α.deriv }

/-- Transitivity of 2-cells.

This composes common extensions by transporting the right leg of `β` through
the inverse of its left leg and then into the apex of `α`. -/
def trans {M N : Term} {p q r : ReductionSeq M N} :
    Homotopy2 p q → Homotopy2 q r → Homotopy2 p r
  | α, β =>
      { deriv := Homotopy2Deriv.trans α.deriv β.deriv }

end Homotopy2

/-- Left whiskering transports a 2-cell along composition on the left. -/
def whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    Homotopy2 (ReductionSeq.concat r p) (ReductionSeq.concat r q) :=
  { deriv := Homotopy2Deriv.whiskerLeft r α.deriv }

/-- Right whiskering transports a 2-cell along composition on the right. -/
def whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p s) (ReductionSeq.concat q s) :=
  { deriv := Homotopy2Deriv.whiskerRight α.deriv s }

/-- Horizontal composition of 2-cells. -/
def hcomp {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Homotopy2 (ReductionSeq.concat p q) (ReductionSeq.concat p' q') :=
  { deriv := Homotopy2Deriv.trans
      (Homotopy2Deriv.whiskerRight α.deriv q)
      (Homotopy2Deriv.whiskerLeft p' β.deriv) }

/-- The associator 2-cell witnessing that concatenation is associative. -/
def associator {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.concat p q) r)
      (ReductionSeq.concat p (ReductionSeq.concat q r)) :=
  Homotopy2.ofEq (ReductionSeq.concat_assoc p q r)

/-- The left unitor. -/
def leftUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.refl M) p) p :=
  Homotopy2.ofEq (ReductionSeq.concat_refl_left p)

/-- The right unitor. -/
def rightUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat p (ReductionSeq.refl N)) p :=
  Homotopy2.ofEq (ReductionSeq.concat_refl_right p)

/-- The fragment of syntactic 2-cells currently supported by the structural
semantic interpretation.

This keeps only the constructors already matched by explicit simplicial
operations in `ExtensionalKan`: reflexivity, equality, symmetry, vertical
composition, and left/right whiskering. The omitted primitive constructor
`diamond` remains part of the full syntax, but it is not included in this
restricted fragment. -/
inductive StructuralHomotopy2 :
    {M N : Term} → ReductionSeq M N → ReductionSeq M N → Type where
  | refl {M N : Term} (p : ReductionSeq M N) : StructuralHomotopy2 p p
  | ofEq {M N : Term} {p q : ReductionSeq M N} :
      p = q → StructuralHomotopy2 p q
  | symm {M N : Term} {p q : ReductionSeq M N} :
      StructuralHomotopy2 p q → StructuralHomotopy2 q p
  | trans {M N : Term} {p q r : ReductionSeq M N} :
      StructuralHomotopy2 p q → StructuralHomotopy2 q r → StructuralHomotopy2 p r
  | whiskerLeft {M N P : Term} (r : ReductionSeq M N)
      {p q : ReductionSeq N P} :
      StructuralHomotopy2 p q →
      StructuralHomotopy2 (ReductionSeq.concat r p) (ReductionSeq.concat r q)
  | whiskerRight {M N P : Term} {p q : ReductionSeq M N} :
      StructuralHomotopy2 p q → (s : ReductionSeq N P) →
      StructuralHomotopy2 (ReductionSeq.concat p s) (ReductionSeq.concat q s)

namespace StructuralHomotopy2

/-- Forget the structural restriction and regard a supported derivation as an
ordinary syntactic 2-cell. -/
def toHomotopy2 {M N : Term} {p q : ReductionSeq M N} :
    StructuralHomotopy2 p q → Homotopy2 p q
  | .refl p => Homotopy2.refl p
  | .ofEq h => Homotopy2.ofEq h
  | .symm α => Homotopy2.symm α.toHomotopy2
  | .trans α β => Homotopy2.trans α.toHomotopy2 β.toHomotopy2
  | .whiskerLeft r α => HigherTerms.whiskerLeft r α.toHomotopy2
  | .whiskerRight α s => HigherTerms.whiskerRight α.toHomotopy2 s

/-- Horizontal composition inside the structurally supported fragment. -/
def hcomp {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : StructuralHomotopy2 p p') (β : StructuralHomotopy2 q q') :
    StructuralHomotopy2 (ReductionSeq.concat p q) (ReductionSeq.concat p' q') :=
  .trans (.whiskerRight α q) (.whiskerLeft p' β)

/-- The associator 2-cell lies in the structurally supported fragment because
it is generated by literal equality of concatenations. -/
def associator {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    StructuralHomotopy2 (ReductionSeq.concat (ReductionSeq.concat p q) r)
      (ReductionSeq.concat p (ReductionSeq.concat q r)) :=
  .ofEq (ReductionSeq.concat_assoc p q r)

/-- The left unitor lies in the structurally supported fragment. -/
def leftUnitor {M N : Term} (p : ReductionSeq M N) :
    StructuralHomotopy2 (ReductionSeq.concat (ReductionSeq.refl M) p) p :=
  .ofEq (ReductionSeq.concat_refl_left p)

/-- The right unitor lies in the structurally supported fragment. -/
def rightUnitor {M N : Term} (p : ReductionSeq M N) :
    StructuralHomotopy2 (ReductionSeq.concat p (ReductionSeq.refl N)) p :=
  .ofEq (ReductionSeq.concat_refl_right p)

end StructuralHomotopy2

/-- A 3-cell between parallel 2-cells is an explicit proof-relevant coherence
derivation. -/
inductive Homotopy3Deriv :
    {M N : Term} → {p q : ReductionSeq M N} →
    (α β : Homotopy2 p q) → Type where
  | refl {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
      Homotopy3Deriv α α
  | ofEq {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q} :
      α = β → Homotopy3Deriv α β
  | symm {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q} :
      Homotopy3Deriv α β → Homotopy3Deriv β α
  | trans {M N : Term} {p q : ReductionSeq M N}
      {α β γ : Homotopy2 p q} :
      Homotopy3Deriv α β → Homotopy3Deriv β γ → Homotopy3Deriv α γ
  | transCongrLeft {M N : Term} {p q r : ReductionSeq M N}
      {η₁ η₂ : Homotopy2 p q} :
      Homotopy3Deriv η₁ η₂ → (θ : Homotopy2 q r) →
      Homotopy3Deriv (Homotopy2.trans η₁ θ) (Homotopy2.trans η₂ θ)
  | transCongrRight {M N : Term} {p q r : ReductionSeq M N}
      (η : Homotopy2 p q) {θ₁ θ₂ : Homotopy2 q r} :
      Homotopy3Deriv θ₁ θ₂ →
      Homotopy3Deriv (Homotopy2.trans η θ₁) (Homotopy2.trans η θ₂)
  | whiskerLeftCongr {L M N : Term} (r : ReductionSeq L M)
      {p q : ReductionSeq M N} {η θ : Homotopy2 p q} :
      Homotopy3Deriv η θ →
      Homotopy3Deriv (whiskerLeft r η) (whiskerLeft r θ)
  | whiskerLeftRefl {M N P : Term} (r : ReductionSeq M N) (p : ReductionSeq N P) :
      Homotopy3Deriv (whiskerLeft r (Homotopy2.refl p))
        (Homotopy2.refl (ReductionSeq.concat r p))
  | whiskerRightRefl {M N P : Term} (p : ReductionSeq M N) (s : ReductionSeq N P) :
      Homotopy3Deriv (whiskerRight (Homotopy2.refl p) s)
        (Homotopy2.refl (ReductionSeq.concat p s))
  | whiskerLeftTrans {M N P : Term} (r : ReductionSeq M N)
      {p q s : ReductionSeq N P} (α : Homotopy2 p q) (β : Homotopy2 q s) :
      Homotopy3Deriv (whiskerLeft r (Homotopy2.trans α β))
        (Homotopy2.trans (whiskerLeft r α) (whiskerLeft r β))
  | whiskerRightTrans {M N P : Term}
      {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s)
      (r : ReductionSeq N P) :
      Homotopy3Deriv (whiskerRight (Homotopy2.trans α β) r)
        (Homotopy2.trans (whiskerRight α r) (whiskerRight β r))
  | whiskerLeftSymm {M N P : Term} (r : ReductionSeq M N)
      {p q : ReductionSeq N P} (α : Homotopy2 p q) :
      Homotopy3Deriv (whiskerLeft r (Homotopy2.symm α))
        (Homotopy2.symm (whiskerLeft r α))
  | whiskerRightSymm {M N P : Term}
      {p q : ReductionSeq M N} (α : Homotopy2 p q) (s : ReductionSeq N P) :
      Homotopy3Deriv (whiskerRight (Homotopy2.symm α) s)
        (Homotopy2.symm (whiskerRight α s))
  | interchange {M N P : Term}
      {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
      (α : Homotopy2 p p') (β : Homotopy2 q q') :
      Homotopy3Deriv (hcomp α β)
        (Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β))
  | interchange' {M N P : Term}
      {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
      (α : Homotopy2 p p') (β : Homotopy2 q q') :
      Homotopy3Deriv (hcomp α β)
        (Homotopy2.trans (whiskerLeft p β) (whiskerRight α q'))
  | pentagon {M N P Q R : Term}
      (p : ReductionSeq M N) (q : ReductionSeq N P)
      (r : ReductionSeq P Q) (s : ReductionSeq Q R) :
      Homotopy3Deriv
        (Homotopy2.trans (associator (ReductionSeq.concat p q) r s)
          (associator p q (ReductionSeq.concat r s)))
        (Homotopy2.trans
          (Homotopy2.trans (whiskerRight (associator p q r) s)
            (associator p (ReductionSeq.concat q r) s))
          (whiskerLeft p (associator q r s)))
  | triangle {M N P : Term}
      (p : ReductionSeq M N) (q : ReductionSeq N P) :
      Homotopy3Deriv
        (Homotopy2.trans (associator p (ReductionSeq.refl N) q)
          (whiskerLeft p (leftUnitor q)))
        (whiskerRight (rightUnitor p) q)
  | invWhiskerLeft {M N P : Term}
      (r : ReductionSeq M N) {p q : ReductionSeq N P}
      (α : Homotopy2 p q) :
      Homotopy3Deriv (Homotopy2.symm (whiskerLeft r α))
        (whiskerLeft r (Homotopy2.symm α))
  | invWhiskerRight {M N P : Term}
      {p q : ReductionSeq M N} (α : Homotopy2 p q)
      (s : ReductionSeq N P) :
      Homotopy3Deriv (Homotopy2.symm (whiskerRight α s))
        (whiskerRight (Homotopy2.symm α) s)

structure Homotopy3 {M N : Term} {p q : ReductionSeq M N}
    (α β : Homotopy2 p q) where
  deriv : Homotopy3Deriv α β

namespace Homotopy3

/-- Reflexivity of 3-cells. -/
def refl {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) : Homotopy3 α α :=
  { deriv := Homotopy3Deriv.refl α }

/-- A 3-cell induced by literal equality of 2-cells. -/
def ofEq {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q}
    (h : α = β) : Homotopy3 α β := by
  cases h
  exact { deriv := Homotopy3Deriv.ofEq rfl }

/-- Build a 3-cell from an explicit derivation token. -/
def ofDeriv {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q}
    (d : Homotopy3Deriv α β) : Homotopy3 α β :=
  { deriv := d }

/-- Symmetry of 3-cells. -/
def symm {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (γ : Homotopy3 α β) : Homotopy3 β α :=
  { deriv := Homotopy3Deriv.symm γ.deriv }

/-- Transitivity of 3-cells by composing coherence derivations. -/
def trans {M N : Term} {p q : ReductionSeq M N}
    {α β γ : Homotopy2 p q} (η₁ : Homotopy3 α β) (η₂ : Homotopy3 β γ) :
    Homotopy3 α γ :=
  { deriv := Homotopy3Deriv.trans η₁.deriv η₂.deriv }

/-- Vertical composition is congruent in its left argument at the explicit
3-cell level. -/
def transCongrLeft {M N : Term} {p q r : ReductionSeq M N}
    {η₁ η₂ : Homotopy2 p q} (Κ : Homotopy3 η₁ η₂) (θ : Homotopy2 q r) :
    Homotopy3 (Homotopy2.trans η₁ θ) (Homotopy2.trans η₂ θ) :=
  { deriv := Homotopy3Deriv.transCongrLeft Κ.deriv θ }

/-- Vertical composition is congruent in its right argument at the explicit
3-cell level. -/
def transCongrRight {M N : Term} {p q r : ReductionSeq M N}
    (η : Homotopy2 p q) {θ₁ θ₂ : Homotopy2 q r} (Κ : Homotopy3 θ₁ θ₂) :
    Homotopy3 (Homotopy2.trans η θ₁) (Homotopy2.trans η θ₂) :=
  { deriv := Homotopy3Deriv.transCongrRight η Κ.deriv }

/-- Left whiskering is congruent on explicit 3-cells. -/
def whiskerLeftCongr {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} {η θ : Homotopy2 p q} (Κ : Homotopy3 η θ) :
    Homotopy3 (whiskerLeft r η) (whiskerLeft r θ) :=
  { deriv := Homotopy3Deriv.whiskerLeftCongr r Κ.deriv }

end Homotopy3

/-- The syntactic 3-cell fragment currently supported by the semantic
3-cell interpretation.

This covers the currently validated endpoint-language fragment, including both
interchange constructors together with triangle, pentagon, and congruence under
vertical composition and left whiskering. -/
inductive StructuralHomotopy3 :
    {M N : Term} → {p q : ReductionSeq M N} →
    (α β : Homotopy2 p q) → Type where
  | refl {M N : Term} {p q : ReductionSeq M N} (α : Homotopy2 p q) :
      StructuralHomotopy3 α α
  | ofEq {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q} :
      α = β → StructuralHomotopy3 α β
  | symm {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q} :
      StructuralHomotopy3 α β → StructuralHomotopy3 β α
  | trans {M N : Term} {p q : ReductionSeq M N}
      {α β γ : Homotopy2 p q} :
      StructuralHomotopy3 α β → StructuralHomotopy3 β γ →
      StructuralHomotopy3 α γ
  | transCongrLeft {M N : Term} {p q r : ReductionSeq M N}
      {η₁ η₂ : Homotopy2 p q} :
      StructuralHomotopy3 η₁ η₂ → (θ : Homotopy2 q r) →
      StructuralHomotopy3 (Homotopy2.trans η₁ θ) (Homotopy2.trans η₂ θ)
  | transCongrRight {M N : Term} {p q r : ReductionSeq M N}
      (η : Homotopy2 p q) {θ₁ θ₂ : Homotopy2 q r} :
      StructuralHomotopy3 θ₁ θ₂ →
      StructuralHomotopy3 (Homotopy2.trans η θ₁) (Homotopy2.trans η θ₂)
  | whiskerLeftCongr {L M N : Term} (r : ReductionSeq L M)
      {p q : ReductionSeq M N} {η θ : Homotopy2 p q} :
      StructuralHomotopy3 η θ →
      StructuralHomotopy3 (whiskerLeft r η) (whiskerLeft r θ)
  | whiskerLeftRefl {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
      StructuralHomotopy3 (whiskerLeft r (Homotopy2.refl p))
        (Homotopy2.refl (ReductionSeq.concat r p))
  | whiskerRightRefl {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
      StructuralHomotopy3 (whiskerRight (Homotopy2.refl p) s)
        (Homotopy2.refl (ReductionSeq.concat p s))
  | whiskerRightTrans {L M N : Term}
      {p q r : ReductionSeq L M} (α : Homotopy2 p q) (β : Homotopy2 q r)
      (s : ReductionSeq M N) :
      StructuralHomotopy3 (whiskerRight (Homotopy2.trans α β) s)
        (Homotopy2.trans (whiskerRight α s) (whiskerRight β s))
  | whiskerLeftTrans {L M N : Term} (r : ReductionSeq L M)
      {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s) :
      StructuralHomotopy3 (whiskerLeft r (Homotopy2.trans α β))
        (Homotopy2.trans (whiskerLeft r α) (whiskerLeft r β))
  | whiskerLeftSymm {L M N : Term} (r : ReductionSeq L M)
      {p q : ReductionSeq M N} (α : Homotopy2 p q) :
      StructuralHomotopy3 (whiskerLeft r (Homotopy2.symm α))
        (Homotopy2.symm (whiskerLeft r α))
  | whiskerRightSymm {L M N : Term}
      {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
      StructuralHomotopy3 (whiskerRight (Homotopy2.symm α) s)
        (Homotopy2.symm (whiskerRight α s))
  | invWhiskerLeft {L M N : Term} (r : ReductionSeq L M)
      {p q : ReductionSeq M N} (α : Homotopy2 p q) :
      StructuralHomotopy3 (Homotopy2.symm (whiskerLeft r α))
        (whiskerLeft r (Homotopy2.symm α))
  | invWhiskerRight {L M N : Term}
      {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
      StructuralHomotopy3 (Homotopy2.symm (whiskerRight α s))
        (whiskerRight (Homotopy2.symm α) s)
  | interchange {M N P : Term}
      {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
      (α : Homotopy2 p p') (β : Homotopy2 q q') :
      StructuralHomotopy3 (hcomp α β)
        (Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β))
  | interchange' {M N P : Term}
      {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
      (α : Homotopy2 p p') (β : Homotopy2 q q') :
      StructuralHomotopy3 (hcomp α β)
        (Homotopy2.trans (whiskerLeft p β) (whiskerRight α q'))
  | pentagon {M N P Q R : Term}
      (p : ReductionSeq M N) (q : ReductionSeq N P)
      (r : ReductionSeq P Q) (s : ReductionSeq Q R) :
      StructuralHomotopy3
        (Homotopy2.trans (associator (ReductionSeq.concat p q) r s)
          (associator p q (ReductionSeq.concat r s)))
        (Homotopy2.trans
          (Homotopy2.trans (whiskerRight (associator p q r) s)
            (associator p (ReductionSeq.concat q r) s))
          (whiskerLeft p (associator q r s)))
  | triangle {M N P : Term}
      (p : ReductionSeq M N) (q : ReductionSeq N P) :
      StructuralHomotopy3
        (Homotopy2.trans (associator p (ReductionSeq.refl N) q)
          (whiskerLeft p (leftUnitor q)))
        (whiskerRight (rightUnitor p) q)

namespace StructuralHomotopy3

/-- Forget the structural restriction and regard a supported derivation as an
ordinary syntactic 3-cell. -/
def toHomotopy3 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} : StructuralHomotopy3 α β → Homotopy3 α β
  | .refl α => Homotopy3.refl α
  | .ofEq h => Homotopy3.ofEq h
  | .symm η => Homotopy3.symm η.toHomotopy3
  | .trans η θ => Homotopy3.trans η.toHomotopy3 θ.toHomotopy3
  | .transCongrLeft η θ =>
      Homotopy3.transCongrLeft η.toHomotopy3 θ
  | .transCongrRight η θ =>
      Homotopy3.transCongrRight η θ.toHomotopy3
  | .whiskerLeftCongr r η =>
      Homotopy3.whiskerLeftCongr r η.toHomotopy3
  | .whiskerLeftRefl r p =>
      Homotopy3.ofDeriv (Homotopy3Deriv.whiskerLeftRefl r p)
  | .whiskerRightRefl p s =>
      Homotopy3.ofDeriv (Homotopy3Deriv.whiskerRightRefl p s)
  | .whiskerRightTrans α β s =>
      Homotopy3.ofDeriv (Homotopy3Deriv.whiskerRightTrans α β s)
  | .whiskerLeftTrans r α β =>
      Homotopy3.ofDeriv (Homotopy3Deriv.whiskerLeftTrans r α β)
  | .whiskerLeftSymm r α =>
      Homotopy3.ofDeriv (Homotopy3Deriv.whiskerLeftSymm r α)
  | .whiskerRightSymm α s =>
      Homotopy3.ofDeriv (Homotopy3Deriv.whiskerRightSymm α s)
  | .invWhiskerLeft r α =>
      Homotopy3.ofDeriv (Homotopy3Deriv.invWhiskerLeft r α)
  | .invWhiskerRight α s =>
      Homotopy3.ofDeriv (Homotopy3Deriv.invWhiskerRight α s)
  | .interchange α β =>
      Homotopy3.ofDeriv (Homotopy3Deriv.interchange α β)
  | .interchange' α β =>
      Homotopy3.ofDeriv (Homotopy3Deriv.interchange' α β)
  | .pentagon p q r s =>
      Homotopy3.ofDeriv (Homotopy3Deriv.pentagon p q r s)
  | .triangle p q =>
      Homotopy3.ofDeriv (Homotopy3Deriv.triangle p q)

end StructuralHomotopy3

namespace Homotopy3Deriv

/-- Every primitive syntactic 3-derivation now lies in the structurally
supported 3-cell fragment. -/
def toStructuralHomotopy3 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} : Homotopy3Deriv α β → StructuralHomotopy3 α β
  | .refl α => .refl α
  | .ofEq h => .ofEq h
  | .symm η => .symm η.toStructuralHomotopy3
  | .trans η θ => .trans η.toStructuralHomotopy3 θ.toStructuralHomotopy3
  | .transCongrLeft η θ => .transCongrLeft η.toStructuralHomotopy3 θ
  | .transCongrRight η θ => .transCongrRight η θ.toStructuralHomotopy3
  | .whiskerLeftCongr r η => .whiskerLeftCongr r η.toStructuralHomotopy3
  | .whiskerLeftRefl r p => .whiskerLeftRefl r p
  | .whiskerRightRefl p s => .whiskerRightRefl p s
  | .whiskerLeftTrans r α β => .whiskerLeftTrans r α β
  | .whiskerRightTrans α β r => .whiskerRightTrans α β r
  | .whiskerLeftSymm r α => .whiskerLeftSymm r α
  | .whiskerRightSymm α s => .whiskerRightSymm α s
  | .interchange α β => .interchange α β
  | .interchange' α β => .interchange' α β
  | .pentagon p q r s => .pentagon p q r s
  | .triangle p q => .triangle p q
  | .invWhiskerLeft r α => .invWhiskerLeft r α
  | .invWhiskerRight α s => .invWhiskerRight α s

end Homotopy3Deriv

namespace Homotopy3

/-- Every syntactic 3-cell can be reflected into the structural fragment used by
the generic semantic interpreter. -/
def toStructuralHomotopy3 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (η : Homotopy3 α β) : StructuralHomotopy3 α β :=
  η.deriv.toStructuralHomotopy3

end Homotopy3

/-! ## Groupoid Structure -/

/-- Right inverse law up to 2-cell. -/
def inv_right_homotopy {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat p p.inv) (ReductionSeq.refl M) :=
  Homotopy2.trans
    (Homotopy2.ofDiamond p (ReductionSeq.refl M) p.inv (ReductionSeq.refl M))
    (Homotopy2.ofEq (ReductionSeq.concat_refl_left (ReductionSeq.refl M)))

/-- Left inverse law up to 2-cell. -/
def inv_left_homotopy {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat p.inv p) (ReductionSeq.refl N) :=
  Homotopy2.trans
    (Homotopy2.ofDiamond p.inv (ReductionSeq.refl N) p (ReductionSeq.refl N))
    (Homotopy2.ofEq (ReductionSeq.concat_refl_left (ReductionSeq.refl N)))

/-- Associativity of concatenation holds up to 2-cell. -/
def concat_assoc_homotopy {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.concat p q) r)
              (ReductionSeq.concat p (ReductionSeq.concat q r)) :=
  Homotopy2.ofEq (ReductionSeq.concat_assoc p q r)

/-! ## Tower Data -/

/-- Explicit higher derivations in an arbitrary type. -/
inductive HigherDeriv {A : Type u} : A → A → Type u where
  | refl (x : A) : HigherDeriv x x
  | symm {x y : A} : HigherDeriv x y → HigherDeriv y x
  | trans {x y z : A} : HigherDeriv x y → HigherDeriv y z → HigherDeriv x z

namespace HigherDeriv

/-- Every abstract higher derivation in the current recursive layer collapses to
ordinary equality of its endpoints. -/
theorem toEq {A : Type u} {x y : A} : HigherDeriv x y → x = y
  | .refl _ => rfl
  | .symm h => (toEq h).symm
  | .trans h₁ h₂ => (toEq h₁).trans (toEq h₂)

end HigherDeriv

/-- The type of cells in the constructive higher λ-model.

Dimensions `0` through `3` are represented explicitly. Above that, the tower is
continued by explicit higher derivations between cells of the previous level. -/
def Cell : Nat → Type
  | 0 => Term
  | 1 => Σ (M N : Term), ReductionSeq M N
  | 2 => Σ (M N : Term) (p q : ReductionSeq M N), Homotopy2 p q
  | 3 => Σ (M N : Term) (p q : ReductionSeq M N) (α β : Homotopy2 p q), Homotopy3 α β
  | n + 4 => Σ (x y : Cell (n + 3)), HigherDeriv x y

namespace Cell

/-- The immediate source boundary of a higher cell. -/
def source : {n : Nat} → Cell (n + 1) → Cell n
  | 0, ⟨M, _, _⟩ => M
  | 1, ⟨M, N, p, _, _⟩ => ⟨M, N, p⟩
  | 2, ⟨M, N, p, q, α, _, _⟩ => ⟨M, N, p, q, α⟩
  | _ + 3, ⟨x, _, _⟩ => x

/-- The immediate target boundary of a higher cell. -/
def target : {n : Nat} → Cell (n + 1) → Cell n
  | 0, ⟨_, N, _⟩ => N
  | 1, ⟨M, N, _, q, _⟩ => ⟨M, N, q⟩
  | 2, ⟨M, N, p, q, _, β, _⟩ => ⟨M, N, p, q, β⟩
  | _ + 3, ⟨_, y, _⟩ => y

/-- Globularity on source boundaries for the recursive higher-cell tower. -/
theorem globular_source : {n : Nat} → (x : Cell (n + 2)) →
    source (source x) = source (target x)
  | 0, ⟨M, N, p, q, α⟩ => by
      -- A 2-cell ⟨M, N, p, q, α⟩ has source = ⟨M,N,p⟩, target = ⟨M,N,q⟩
      let cell : Cell 2 := ⟨M, N, p, q, α⟩
      calc
        source (source cell) = M := by rfl
        _ = source (target cell) := by rfl
  | 1, ⟨M, N, p, q, α, β, η⟩ => by
      let cell : Cell 3 := ⟨M, N, p, q, α, β, η⟩
      let boundary : Cell 1 := ⟨M, N, p⟩
      calc
        source (source cell) = boundary := by rfl
        _ = source (target cell) := by rfl
  | _ + 2, ⟨x, y, h⟩ => by
      cases HigherDeriv.toEq h
      rfl

/-- Globularity on target boundaries for the recursive higher-cell tower. -/
theorem globular_target : {n : Nat} → (x : Cell (n + 2)) →
    target (source x) = target (target x)
  | 0, ⟨M, N, p, q, α⟩ => by
      let cell : Cell 2 := ⟨M, N, p, q, α⟩
      calc
        target (source cell) = N := by rfl
        _ = target (target cell) := by rfl
  | 1, ⟨M, N, p, q, α, β, η⟩ => by
      let cell : Cell 3 := ⟨M, N, p, q, α, β, η⟩
      let boundary : Cell 1 := ⟨M, N, q⟩
      calc
        target (source cell) = boundary := by rfl
        _ = target (target cell) := by rfl
  | _ + 2, ⟨x, y, h⟩ => by
      cases HigherDeriv.toEq h
      rfl

end Cell

/-! ## Homotopic λ-Models -/

/-- A lightweight packaging of the structure used semantically in the paper. -/
structure HomotopicLambdaModel where
  carrier : Type
  app : carrier → carrier → carrier
  lam : (carrier → carrier) → carrier
  beta : ∀ f x, app (lam f) x = f x
  ext : ∀ M N, (∀ x, app M x = app N x) → M = N
  PathSpace : carrier → carrier → Type
  Path2 : {M N : carrier} → PathSpace M N → PathSpace M N → Type
  path2_refl : ∀ M N (p : PathSpace M N), Path2 p p

/-! ## Weak ω-Groupoid Data -/

/-- The generic low-dimensional omega-groupoid interface specialized to the
lambda-calculus higher-path core.

The `refl2` field packages the canonical reflexive 2-cell constructor available
in the current higher-path core. -/
abbrev LambdaOmegaGroupoidData :=
  HigherLambdaModel.Simplicial.OmegaGroupoidData

/-- The λ-terms carry the expected low-dimensional groupoid data, with
canonical reflexive 2-cells. -/
def lambdaOmegaGroupoidData : LambdaOmegaGroupoidData where
  Obj := Term
  Hom := ReductionSeq
  id := ReductionSeq.refl
  comp := ReductionSeq.concat
  inv := ReductionSeq.inv
  Hom2 := Homotopy2
  refl2 := Homotopy2.refl

end HigherLambdaModel.Lambda.HigherTerms
