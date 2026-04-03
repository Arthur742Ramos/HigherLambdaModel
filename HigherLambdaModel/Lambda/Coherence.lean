/-
# Coherence Laws for the Weak ω-Groupoid Structure on λ-Terms

This module records coherence witnesses for the explicit higher-cell structure on
λ-terms. Unlike the earlier proof-irrelevant presentation, the current version
expresses coherence by actual 3-cells rather than strict equalities of 2-cells.
-/

import HigherLambdaModel.Lambda.HigherTerms

namespace HigherLambdaModel.Lambda.Coherence

open Term
open HigherLambdaModel.Lambda.HigherTerms

/-! ## Whiskering Operations -/

/-- Left whiskering transports a 2-cell along composition on the left. -/
def whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    Homotopy2 (ReductionSeq.concat r p) (ReductionSeq.concat r q) :=
  HigherTerms.whiskerLeft r α

/-- Right whiskering transports a 2-cell along composition on the right. -/
def whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p s) (ReductionSeq.concat q s) :=
  HigherTerms.whiskerRight α s

/-- Horizontal composition of 2-cells. -/
def hcomp {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Homotopy2 (ReductionSeq.concat p q) (ReductionSeq.concat p' q') :=
  HigherTerms.hcomp α β

/-! ## Whiskering Properties -/

/-- Left whiskering preserves identity 2-cells up to a 3-cell. -/
def whiskerLeft_refl {M N P : Term}
    (r : ReductionSeq M N) (p : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerLeft r (Homotopy2.refl p))
      (Homotopy2.refl (ReductionSeq.concat r p)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerLeftRefl r p)

/-- Right whiskering preserves identity 2-cells up to a 3-cell. -/
def whiskerRight_refl {M N P : Term}
    (p : ReductionSeq M N) (s : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerRight (Homotopy2.refl p) s)
      (Homotopy2.refl (ReductionSeq.concat p s)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerRightRefl p s)

/-- Left whiskering preserves vertical composition up to a 3-cell. -/
def whiskerLeft_trans {M N P : Term}
    (r : ReductionSeq M N) {p q s : ReductionSeq N P}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    HigherTerms.Homotopy3 (whiskerLeft r (Homotopy2.trans α β))
      (Homotopy2.trans (whiskerLeft r α) (whiskerLeft r β)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerLeftTrans r α β)

/-- Right whiskering preserves vertical composition up to a 3-cell. -/
def whiskerRight_trans {M N P : Term}
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s)
    (r : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerRight (Homotopy2.trans α β) r)
      (Homotopy2.trans (whiskerRight α r) (whiskerRight β r)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerRightTrans α β r)

/-- Left whiskering preserves symmetry up to a 3-cell. -/
def whiskerLeft_symm {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    HigherTerms.Homotopy3 (whiskerLeft r (Homotopy2.symm α))
      (Homotopy2.symm (whiskerLeft r α)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerLeftSymm r α)

/-- Right whiskering preserves symmetry up to a 3-cell. -/
def whiskerRight_symm {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    HigherTerms.Homotopy3 (whiskerRight (Homotopy2.symm α) s)
      (Homotopy2.symm (whiskerRight α s)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.whiskerRightSymm α s)

/-! ## Interchange Law -/

/-- Interchange is witnessed by a 3-cell. -/
def interchange {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HigherTerms.Homotopy3 (hcomp α β)
      (Homotopy2.trans (whiskerRight α q) (whiskerLeft p' β)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.interchange α β)

/-- Alternative interchange witness using the other parenthesization. -/
def interchange' {M N P : Term}
    {p p' : ReductionSeq M N} {q q' : ReductionSeq N P}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HigherTerms.Homotopy3 (hcomp α β)
      (Homotopy2.trans (whiskerLeft p β) (whiskerRight α q')) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.interchange' α β)

/-! ## Associativity Coherence (Pentagon) -/

/-- The associator 2-cell witnessing that concatenation is associative. -/
def associator {M N P Q : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.concat p q) r)
      (ReductionSeq.concat p (ReductionSeq.concat q r)) :=
  HigherTerms.associator p q r

/-- Pentagon coherence is witnessed by a 3-cell. -/
def pentagon {M N P Q R : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P)
    (r : ReductionSeq P Q) (s : ReductionSeq Q R) :
    HigherTerms.Homotopy3
      (Homotopy2.trans (associator (ReductionSeq.concat p q) r s)
        (associator p q (ReductionSeq.concat r s)))
      (Homotopy2.trans
        (Homotopy2.trans (whiskerRight (associator p q r) s)
          (associator p (ReductionSeq.concat q r) s))
        (whiskerLeft p (associator q r s))) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.pentagon p q r s)

/-! ## Unit Coherence (Triangle) -/

/-- The left unitor. -/
def leftUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat (ReductionSeq.refl M) p) p :=
  HigherTerms.leftUnitor p

/-- The right unitor. -/
def rightUnitor {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 (ReductionSeq.concat p (ReductionSeq.refl N)) p :=
  HigherTerms.rightUnitor p

/-- Triangle coherence is witnessed by a 3-cell. -/
def triangle {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) :
    HigherTerms.Homotopy3
      (Homotopy2.trans (associator p (ReductionSeq.refl N) q)
        (whiskerLeft p (leftUnitor q)))
      (whiskerRight (rightUnitor p) q) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.triangle p q)

/-! ## Reflexive Coherence -/

/-- Every 2-cell admits its reflexive 3-cell. -/
def coherence_refl {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    HigherTerms.Homotopy3 α α :=
  HigherTerms.Homotopy3.refl α

/-! ## Coherence for Inverses -/

/-- Inverse of refl is homotopic to refl. -/
def inv_refl_homotopy {M : Term} :
    Homotopy2 (ReductionSeq.refl M).inv (ReductionSeq.refl M) :=
  Homotopy2.ofEq rfl

/-- Inverse distributes over composition up to homotopy. -/
def inv_concat {M N P : Term}
    (p : ReductionSeq M N) (q : ReductionSeq N P) :
    Homotopy2 (ReductionSeq.concat p q).inv
              (ReductionSeq.concat q.inv p.inv) :=
  Homotopy2.ofEq (ReductionSeq.inv_concat p q)

/-- Double inverse returns to the original path up to homotopy. -/
def inv_inv {M N : Term} (p : ReductionSeq M N) :
    Homotopy2 p.inv.inv p :=
  Homotopy2.ofEq (ReductionSeq.inv_inv p)

/-- Inverse commutes with left whiskering up to a 3-cell. -/
def inv_whiskerLeft {M N P : Term}
    (r : ReductionSeq M N) {p q : ReductionSeq N P}
    (α : Homotopy2 p q) :
    HigherTerms.Homotopy3 (Homotopy2.symm (whiskerLeft r α))
      (whiskerLeft r (Homotopy2.symm α)) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.invWhiskerLeft r α)

/-- Inverse commutes with right whiskering up to a 3-cell. -/
def inv_whiskerRight {M N P : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q)
    (s : ReductionSeq N P) :
    HigherTerms.Homotopy3 (Homotopy2.symm (whiskerRight α s))
      (whiskerRight (Homotopy2.symm α) s) :=
  HigherTerms.Homotopy3.ofDeriv (HigherTerms.Homotopy3Deriv.invWhiskerRight α s)

/-! ## Higher Reflexivity -/

/-- Every 2-cell admits its reflexive 3-cell. -/
def homotopy3_refl {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) : HigherTerms.Homotopy3 α α :=
  HigherTerms.Homotopy3.refl α

/-- Every 3-cell admits its reflexive 4-cell in the recursive higher tower. -/
def homotopy4_refl {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (η : HigherTerms.Homotopy3 α β) :
    HigherTerms.HigherDeriv η η :=
  HigherTerms.HigherDeriv.refl η

/-- Every 4-cell admits its reflexive 5-cell in the recursive higher tower. -/
def homotopy5_refl {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} {η θ : HigherTerms.Homotopy3 α β}
    (ω : HigherTerms.HigherDeriv η θ) :
    HigherTerms.HigherDeriv ω ω :=
  HigherTerms.HigherDeriv.refl ω

/-! ## The Weak ω-Groupoid Structure -/

/-- The generic omega-groupoid core specialized to λ-terms. -/
abbrev LambdaOmegaGroupoid :=
  HigherLambdaModel.Simplicial.OmegaGroupoid

/-- The canonical weak ω-groupoid structure on λ-terms. -/
def lambdaOmegaGroupoid : LambdaOmegaGroupoid := {
  Obj := Term
  Hom := ReductionSeq
  id := ReductionSeq.refl
  comp := ReductionSeq.concat
  inv := ReductionSeq.inv
  Hom2 := Homotopy2
  refl2 := Homotopy2.refl
  Hom3 := HigherTerms.Homotopy3
  Hom4 := fun {_} {_} {_} {_} {_} {_} η θ => HigherTerms.HigherDeriv η θ
  Hom5 := fun {_} {_} {_} {_} {_} {_} {_} {_} ω ω' => HigherTerms.HigherDeriv ω ω'
  symm2 := fun α => Homotopy2.symm α
  trans2 := fun α β => Homotopy2.trans α β
  whiskerLeft := fun {M} {N} {P} r {p} {q} α =>
    HigherLambdaModel.Lambda.Coherence.whiskerLeft (M := M) (N := N) (P := P) r
      (p := p) (q := q) α
  whiskerRight := fun {M} {N} {P} {p} {q} α s =>
    HigherLambdaModel.Lambda.Coherence.whiskerRight (M := M) (N := N) (P := P)
      (p := p) (q := q) α s
  hcomp := fun {M} {N} {P} {p} {p'} {q} {q'} α β =>
    HigherLambdaModel.Lambda.Coherence.hcomp (M := M) (N := N) (P := P)
      (p := p) (p' := p') (q := q) (q' := q') α β
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  inv_right := inv_right_homotopy
  inv_left := inv_left_homotopy
  hom3_refl := fun α => coherence_refl α
  hom4_refl := fun η => homotopy4_refl η
  hom5_refl := fun ω => homotopy5_refl ω
  pentagon_coh := pentagon
  triangle_coh := triangle
  interchange_coh := interchange
}

/-! ## Generic Coherence Packaging -/

/-- A lightweight equivalence between two sorts. This keeps the generic
coherence theorem independent of any extra equivalence library while still
working uniformly for all tower levels. -/
structure SortEquiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

namespace SortEquiv

/-- Reflexive equivalence on any sort. -/
def refl (α : Sort u) : SortEquiv α α where
  toFun := id
  invFun := id
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

end SortEquiv

/-- The packed 0-cells carried by a reflexive globular tower. -/
abbrev Tower0 (T : HigherLambdaModel.Simplicial.ReflexiveGlobularTower) : Type _ :=
  T.Cell0

/-- The packed 1-cells carried by a reflexive globular tower. -/
abbrev Tower1 (T : HigherLambdaModel.Simplicial.ReflexiveGlobularTower) : Type _ :=
  Σ (M N : T.Cell0), T.Cell1 M N

/-- The packed 2-cells carried by a reflexive globular tower. -/
abbrev Tower2 (T : HigherLambdaModel.Simplicial.ReflexiveGlobularTower) : Type _ :=
  Σ (M N : T.Cell0) (p q : T.Cell1 M N), T.Cell2 p q

/-- The packed 3-cells carried by a reflexive globular tower. -/
abbrev Tower3 (T : HigherLambdaModel.Simplicial.ReflexiveGlobularTower) : Type _ :=
  Σ (M N : T.Cell0) (p q : T.Cell1 M N) (α β : T.Cell2 p q), T.Cell3 α β

/-- The packed 4-cells carried by a reflexive globular tower. -/
abbrev Tower4 (T : HigherLambdaModel.Simplicial.ReflexiveGlobularTower) : Type _ :=
  Σ (M N : T.Cell0) (p q : T.Cell1 M N) (α β : T.Cell2 p q)
    (η θ : T.Cell3 α β), T.Cell4 η θ

/-- The packed 5-cells carried by a reflexive globular tower. -/
abbrev Tower5 (T : HigherLambdaModel.Simplicial.ReflexiveGlobularTower) : Type _ :=
  Σ (M N : T.Cell0) (p q : T.Cell1 M N) (α β : T.Cell2 p q)
    (η θ : T.Cell3 α β) (ω ξ : T.Cell4 η θ), T.Cell5 ω ξ

/-- An admissible higher λ-model consists of an all-dimensional conversion
tower together with a low-dimensional omega-groupoid core, expressed through
the shared simplicial API. The low-dimensional equivalences identify the tower
with the canonical reflexive tower induced by the omega-groupoid, while the
next two dimensions are required only to admit a realization map into the full
tower. -/
structure AdmissibleHigherLambdaModel where
  tower : HigherLambdaModel.Simplicial.GlobularTower
  omegaGroupoid : HigherLambdaModel.Simplicial.OmegaGroupoid
  cell0Equiv : SortEquiv (tower.Cell 0) (Tower0 (omegaGroupoid.toReflexiveGlobularTower))
  cell1Equiv : SortEquiv (tower.Cell 1) (Tower1 (omegaGroupoid.toReflexiveGlobularTower))
  cell2Equiv : SortEquiv (tower.Cell 2) (Tower2 (omegaGroupoid.toReflexiveGlobularTower))
  cell3Equiv : SortEquiv (tower.Cell 3) (Tower3 (omegaGroupoid.toReflexiveGlobularTower))
  realize4 : Tower4 (omegaGroupoid.toReflexiveGlobularTower) → tower.Cell 4
  realize5 : Tower5 (omegaGroupoid.toReflexiveGlobularTower) → tower.Cell 5

/-- The generic coherence theorem packages the canonical reflexive tower
realized by an admissible higher λ-model. -/
abbrev realizedTower (A : AdmissibleHigherLambdaModel) :
    HigherLambdaModel.Simplicial.ReflexiveGlobularTower :=
  A.omegaGroupoid.toReflexiveGlobularTower

/-- The generic coherence theorem packages the canonical reflexive tower
realized by an admissible higher λ-model. -/
structure HigherConversionCoherence (A : AdmissibleHigherLambdaModel) where
  cell0Equiv : SortEquiv (A.tower.Cell 0) (Tower0 (realizedTower A))
  cell1Equiv : SortEquiv (A.tower.Cell 1) (Tower1 (realizedTower A))
  cell2Equiv : SortEquiv (A.tower.Cell 2) (Tower2 (realizedTower A))
  cell3Equiv : SortEquiv (A.tower.Cell 3) (Tower3 (realizedTower A))
  realize4 : Tower4 (realizedTower A) → A.tower.Cell 4
  realize5 : Tower5 (realizedTower A) → A.tower.Cell 5

/-- Data-level form of the generic coherence theorem. -/
def higherConversionCoherenceData (A : AdmissibleHigherLambdaModel) :
    HigherConversionCoherence A where
  cell0Equiv := A.cell0Equiv
  cell1Equiv := A.cell1Equiv
  cell2Equiv := A.cell2Equiv
  cell3Equiv := A.cell3Equiv
  realize4 := A.realize4
  realize5 := A.realize5

/-- In every admissible higher λ-model, the full higher-conversion algebra
realizes the intended omega-groupoid core through the canonical simplicial API.
-/
theorem higherConversions_form_omegaGroupoid (A : AdmissibleHigherLambdaModel) :
    Nonempty (HigherConversionCoherence A) := by
  exact ⟨(higherConversionCoherenceData A : HigherConversionCoherence A)⟩

end HigherLambdaModel.Lambda.Coherence
